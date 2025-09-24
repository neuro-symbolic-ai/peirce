from abc import ABC, abstractmethod
from typing import List, Optional
import numpy as np

class RetrievalModel(ABC):
    """
    Abstract base class for retrieval models.
    """

    @abstractmethod
    def query(self, queries_list: List[str], top_k: Optional[int] = None, **kwargs) -> np.ndarray:
        """
        Abstract method to retrieve documents based on a query list.
        :param queries_list: A list of queries.
        :param top_k: Optional; number of top results to return.
        :param kwargs: Additional parameters for model-specific logic.
        """
        pass

    def supports_top_q(self) -> bool:
        """
        Indicates whether the model supports the `top_q` parameter.
        Models that don't need this will return False (default).
        """
        return False
