from abc import ABC, abstractmethod
from typing import Optional


class FormalisationModel(ABC):
    def __init__(self, llm, prompt_dict: Optional[dict] = None):
        self.llm = llm
        self.code = ''
        self.prompt_dict = prompt_dict

    @abstractmethod
    def formalise(self, *args, **kwargs):
        pass

    @abstractmethod
    def save_formalised_kb(self, *args, **kwargs):
        pass
