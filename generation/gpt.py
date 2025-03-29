from prompt.prompt_model import PromptModel
from openai import OpenAI
from typing import Optional
import tenacity
import re
from generation.abstract import GenerativeModel


class GPT(GenerativeModel):
    def __init__(self, model_name, api_key, prompt_model=None):
        super().__init__(model_name, prompt_model)
        self.api_key = api_key
        self.client = OpenAI(api_key=self.api_key)
        if prompt_model is None:
            self.prompt_model = PromptModel()

    # handle rate limit
    @tenacity.retry(wait=tenacity.wait_exponential(
            multiplier=1, min=4, max=30))
    def completion_with_backoff(self, **kwargs):
        try:
            return self.client.chat.completions.create(**kwargs)
        except Exception as e:
            print(f'Error: {e}')
            raise e

    def generate(self,
                 model_prompt_dir: str,
                 prompt_name: str,
                 prefix: Optional[str] = None,
                 numbered_list: Optional[bool] = False,
                 remove_number: Optional[bool] = False,
                 test: Optional[bool] = False,
                 **replacements) -> str:
        """
        Generates a response from the LLM model.

        Parameters:
        - model_prompt_dir (str): The directory of the model prompt.
        - prompt_name (str): The name of the prompt.
        - prefix (str, optional): A prefix to match before the numbered list.
        - numbered_list (bool, optional): If True, the response will be
          extracted as a numbered list.
        - remove_number (bool, optional): If True, the numbered list will
          be cleaned of numbering.
        """
        system_prompt, user_prompt = self.prompt_model.process_prompt(
            model_name=model_prompt_dir,
            prompt_name=prompt_name,
            **replacements
        )

        response = None
        try:
            response = self.completion_with_backoff(
                # llm model settings
                model=self.model_name,
                temperature=0,
                frequency_penalty=0,
                max_tokens=4096,
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user", "content": user_prompt}
                ]
            )
        except Exception as e:
            print(f'Error: {e}')
            return
        result = response.choices[0].message.content
        if test:
            print(result)
        # post processing
        if "```" in result:
            result = self.extract_code(result)

        if prefix and prefix in result:
            parts = result.split(prefix, 1)
            if len(parts) > 1:
                result = parts[1].strip()

                if numbered_list and remove_number:
                    result = re.sub(r'\d+\.\s*', '', result)
                    result = '\n'.join(result.splitlines()).strip()
        elif numbered_list:
            result = self.extract_numbered_list(result, None, remove_number)
        return result
