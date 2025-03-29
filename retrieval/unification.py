from .abstract import RetrievalModel
from rank_bm25 import BM25Okapi
from nltk.tokenize import word_tokenize
from tqdm import tqdm
import numpy as np
from typing import List, Optional


# UNIFICATION RETRIEVAL MODEL
class UnificationModel(RetrievalModel):
    """
    Unification-based retrieval model that computes scores based on premises and hypotheses.
    """

    def __init__(self, corpus: List, explanation_corpus: List):
        """
        Initialize the UnificationModel with the provided corpus and explanation corpus.

        :param corpus: A list of documents.
        :param explanation_corpus: A list of hypotheses and their corresponding premises.
        """
        super().__init__()
        self._pre_process(corpus, explanation_corpus)

    def _pre_process(self, corpus: List, explanation_corpus: List) -> None:
        """
        Preprocess the corpus by mapping hypotheses to their premises and tokenizing the documents.

        :param corpus: A list of documents.
        :param explanation_corpus: A list of hypotheses and their corresponding premises.
        """
        self.corpus = corpus
        self.premises_index = []  # Indexes of premises corresponding to each hypothesis
        self.hypothesis_corpus = []  # List of hypothesis statements

        for hypothesis in tqdm(explanation_corpus, desc="Preprocessing - Unification"):
            premises_index = []
            self.hypothesis_corpus.append(hypothesis.surface)

            # Find the index of each premise in the corpus
            for premise in hypothesis.premises:
                if premise in corpus:
                    premises_index.append(corpus.index(premise))

            self.premises_index.append(premises_index)

        # Tokenize the hypothesis documents
        tokenized_hypotheses_corpus = [word_tokenize(stt.lower()) for stt in self.hypothesis_corpus]

        # Initialize BM25 with the tokenized hypothesis corpus
        self.model = BM25Okapi(tokenized_hypotheses_corpus)

    def query(self, queries_list: List[str], top_k: Optional[int] = None, top_q: Optional[int] = None, return_cases: Optional[bool]= False) -> np.ndarray:
        """
        Retrieve and rank premises based on hypotheses and unification scores.

        :param queries_list: A list of query strings.
        :param top_k: Optional; number of top premises to return.
        :param top_q: Optional; number of top hypotheses to consider.
        :return: A NumPy array of unification scores or ranked premises.
        """
        results = []
        similar_cases = []
        for query_string in tqdm(queries_list, desc="Unification - Processing queries"):
            # Tokenize the query
            tokenized_query = word_tokenize(query_string.lower())

            # Initialize the unification scores for premises
            unification_scores = np.zeros(len(self.corpus))

            # Get BM25 scores for the query against the hypothesis corpus
            hypotheses_scores = np.array(self.model.get_scores(tokenized_query))
            ranked_hypotheses = sorted(enumerate(hypotheses_scores), key=lambda x: x[1], reverse=True)

            # Optionally limit the number of top hypotheses to consider
            if top_q:
                ranked_hypotheses = ranked_hypotheses[:top_q]

            similar_cases.append(ranked_hypotheses)

            # Accumulate scores for the premises based on the hypothesis scores
            for res in ranked_hypotheses:
                for premise_index in self.premises_index[res[0]]:
                    unification_scores[premise_index] += res[1]

            if top_k:
                # Sort and rank the premises by their unification scores
                ranked_premises = sorted(enumerate(unification_scores), key=lambda x: x[1], reverse=True)
                ranked_premises = np.array(ranked_premises[:top_k])
                results.append(ranked_premises)
            else:
                results.append(unification_scores)

        if return_cases:
            return np.array(results), np.array(similar_cases)
        else:
            return np.array(results)
    
    def supports_top_q(self) -> bool:
        """
        UnificationModel supports the `top_q` parameter.
        """
        return True