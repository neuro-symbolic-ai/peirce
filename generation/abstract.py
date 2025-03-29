from abc import ABC, abstractmethod
import re
from typing import Optional


class GenerativeModel(ABC):
    def __init__(self, model_name,
                 prompt_model=None):
        self.model_name = model_name
        self.prompt_model = prompt_model

    @abstractmethod
    def generate(self, *args, **kwargs):
        pass

    def extract_code(self, result):
        pattern = r"```(.*?)```"
        match = re.search(pattern, result, re.DOTALL)
        if match:
            result = match.group(1)
        return result

    def extract_numbered_list(self, model_reponse: str,
                          prefix: Optional[str] = None,
                          remove_number: Optional[bool] = False) -> str:
        """
        Extract content after a specific prefix or numbered list.
        
        Parameters:
        - model_reponse (str): Input string from which to extract content
        - prefix (str, optional): Prefix to match. If provided, extract content after this prefix
        - remove_number (bool, optional): If True, remove numbers from the extracted content
        """
        if prefix:
            parts = model_reponse.split(prefix, 1)
            if len(parts) > 1:
                extracted = parts[1].strip()
                
                if remove_number and re.search(r'^\d+\.', extracted, re.MULTILINE):
                    cleaned = re.sub(r'\d+\.\s*', '', extracted)
                    return '\n'.join(cleaned.splitlines()).strip()
                else:
                    return extracted
            else:
                extracted = model_reponse
        else:
            numbered_list_pattern = re.compile(r'(\d+\..*?(?:\n|$))+',
                                            re.IGNORECASE | re.DOTALL)
            match = numbered_list_pattern.search(model_reponse)
            extracted = match.group(0) if match else model_reponse

        if remove_number:
            cleaned = re.sub(r'\d+\.\s*', '', extracted)
            return '\n'.join(cleaned.splitlines()).strip()
        else:
            return extracted
