from .abstract import RetrievalModel
from rank_bm25 import BM25Okapi
from nltk.tokenize import word_tokenize
from tqdm import tqdm
import numpy as np
from typing import List, Optional

# BM25 RETRIEVAL MODEL
class BM25Model(RetrievalModel):
    """
    BM25-based retrieval model that uses tokenized documents for ranking.
    """

    def __init__(self, corpus: List):
        """
        Initialize the BM25Model with the provided corpus and preprocess the corpus.

        :param corpus: A list of documents to be used in the BM25 model.
        """
        super().__init__()
        self._pre_process(corpus)

    def _pre_process(self, corpus: List) -> None:
        """
        Preprocess the corpus by tokenizing the documents and initializing the BM25 model.

        :param corpus: A list of documents to be preprocessed.
        """
        # Extract surface forms from the corpus
        self.corpus = corpus
        self.statements = [stt.surface for stt in tqdm(corpus, desc="Preprocessing - BM25")]

        # Tokenize each document in the corpus
        tokenized_corpus = [word_tokenize(stt.lower()) for stt in self.statements]

        # Initialize the BM25 model using the tokenized corpus
        self.model = BM25Okapi(tokenized_corpus)

    def query(self, queries_list: List[str], top_k: Optional[int] = None) -> np.ndarray:
        """
        Retrieve and rank documents using BM25 based on the given queries.

        :param queries_list: A list of query strings.
        :param top_k: Optional; number of top results to return.
        :return: A NumPy array containing ranked documents or BM25 scores for each query.
        """
        results = []
        for query_string in tqdm(queries_list, desc="BM25 - Processing queries"):
            # Tokenize the query
            tokenized_query = word_tokenize(query_string.lower())

            # Get BM25 scores for the query against the corpus
            stt_scores = np.array(self.model.get_scores(tokenized_query))

            if top_k:
                # Sort and rank the documents by their BM25 scores
                ranked_stts = sorted(enumerate(stt_scores), key=lambda x: x[1], reverse=True)
                ranked_stts = np.array(ranked_stts[:top_k])
                results.append(ranked_stts)
            else:
                results.append(stt_scores)

        return np.array(results)