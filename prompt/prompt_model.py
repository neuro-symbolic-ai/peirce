import re
from pathlib import Path


class PromptModel:
    def __init__(self):
        self.base_path = Path('./prompt/prompts')

    def replace_prompt_content(self, content, replacements):
        pattern = r'\{([^}]+)\}'
        return re.sub(pattern,
                      lambda m: str(replacements.get(m.group(1), m.group(0))),
                      content)

    def process_prompt(self, model_name, prompt_name, **replacements):
        prompt_path = self.base_path / f'{model_name}/{prompt_name}'

        with open(prompt_path, 'r', encoding='utf-8') as f:
            content = f.read()

        content = self.replace_prompt_content(content, replacements)
        system_prompt, user_prompt = map(str.strip, content.split('USER: '))
        system_prompt = system_prompt.replace('SYSTEM: ', '')

        return system_prompt, user_prompt
