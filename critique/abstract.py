from abc import ABC, abstractmethod
from typing import Optional


class CritiqueModel(ABC):
    def __init__(self, generative_model,
                 prompt_dict: Optional[dict] = None,
                 type: Optional[str] = None):
        self.generative_model = generative_model
        self.prompt_dict = prompt_dict
        self.type = type

    @abstractmethod
    def critique(self, *args, **kwargs):
        pass

    @abstractmethod
    def shutdown(self, *args, **kwargs):
        pass
