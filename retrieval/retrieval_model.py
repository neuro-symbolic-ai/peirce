from abc import ABC, abstractmethod
from rank_bm25 import BM25Okapi
from sentence_transformers import SentenceTransformer
from nltk.tokenize import word_tokenize
from tqdm import tqdm
import numpy as np
from typing import List, Optional


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


# SENTENCE TRANSFORMER RETRIEVAL MODEL
class SentenceTransformerModel(RetrievalModel):
    """
    Retrieval model based on Sentence Transformers for encoding and ranking documents.
    """

    def __init__(self, corpus: List, model_name: str):
        """
        Initialize the SentenceTransformerModel with the provided corpus and model.

        :param corpus: A list of documents to be encoded.
        :param model_name: The name of the pretrained sentence transformer model to use.
        """
        super().__init__()
        self._pre_process(corpus, model_name)

    def _pre_process(self, corpus: List, model_name: str) -> None:
        """
        Preprocess the corpus by encoding the documents using the sentence transformer.

        :param corpus: A list of documents to be encoded.
        :param model_name: The name of the sentence transformer model to use.
        """
        # Extract surface forms from the corpus
        self.corpus = corpus
        self.statements = [stt.surface for stt in corpus]

        # Load the sentence transformer model
        self.model = SentenceTransformer(model_name)

        # Encode the corpus using the sentence transformer model
        self.corpus_embeddings = self.model.encode(self.statements, show_progress_bar=True)

    def query(self, queries_list: List[str], top_k: Optional[int] = None) -> np.ndarray:
        """
        Retrieve and rank documents using cosine similarity based on encoded queries.

        :param queries_list: A list of query strings.
        :param top_k: Optional; number of top results to return.
        :return: A NumPy array of cosine similarity scores or ranked results.
        """
        results = []
        for query_string in tqdm(queries_list, desc="SentenceTransformer - Processing queries"):
            # Encode the query string
            query_embedding = self.model.encode(query_string, convert_to_tensor=True)

            # Compute cosine similarity between the query and the corpus
            similarity_scores = self.model.similarity(query_embedding, self.corpus_embeddings)

            if top_k:
                # Sort and rank documents by their similarity scores
                ranked_stts = [(score[0], score[1].item()) for score in sorted(enumerate(similarity_scores[0]), key=lambda x: x[1], reverse=True)]
                ranked_stts = np.array(ranked_stts[:top_k])
                results.append(ranked_stts)
            else:
                results.append(np.array(similarity_scores))

        return np.array(results)


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
    

# Ensemble Model
class EnsembleModel(RetrievalModel):
    """
    Ensemble model that combines the scores from multiple retrieval models using a weighted sum.
    """

    def __init__(self, models: List[RetrievalModel], weights: Optional[List[float]] = None):
        """
        Initializes the EnsembleModel.

        :param models: A list of RetrievalModel objects to be ensembled.
        :param weights: A list of weights for each model. If None, equal weights are used.
        :raises ValueError: If the number of weights does not match the number of models.
        """
        super().__init__()
        self._pre_process(models, weights)

    def _pre_process(self, models: List[RetrievalModel], weights: Optional[List[float]] = None) -> None:
        """
        Preprocess the models and weights for the ensemble.

        :param models: A list of RetrievalModel objects to be ensembled.
        :param weights: A list of weights for each model. If None, equal weights are used.
        :raises ValueError: If the number of weights does not match the number of models.
        """
        self.models = models

        if weights is None:
            self.weights = np.ones(len(models))  # Assign equal weights
        else:
            if len(weights) != len(models):
                raise ValueError(f"Number of weights ({len(weights)}) must match the number of models ({len(models)}).")
            self.weights = np.array(weights)

        self.weights /= self.weights.sum()  # Normalize weights to sum to 1

    def query(self, queries_list: List[str], top_k: Optional[int] = None, top_q: Optional[int] = None) -> np.ndarray:
        """
        Perform an ensemble of the query results from multiple models using a weighted sum of scores.

        :param queries_list: A list of query strings to retrieve results for.
        :param top_k: Optional; the number of top results to return.
        :param top_q: Optional; number of top hypotheses to consider for models that support it.
        :return: A NumPy array of the ensembled scores and indices.
        """
        num_queries = len(queries_list)
        num_facts = len(self.models[0].corpus)
        ensemble_scores = np.zeros((num_queries, num_facts))

        # Collect scores from all models
        all_model_scores = []
        for model in self.models:
            if hasattr(model, 'supports_top_q') and model.supports_top_q():
                model_scores = model.query(queries_list, top_k=None, top_q=top_q)
            else:
                model_scores = model.query(queries_list, top_k=None)
            all_model_scores.append(np.array(model_scores))
        
        # Stack model scores to shape (num_models, num_queries, num_facts)
        all_model_scores = np.stack(all_model_scores)

        # Compute weighted sum
        ensemble_scores = np.tensordot(all_model_scores, self.weights, axes=([0], [0]))

        # Optionally return the top_k results for each query
        ensemble_results = []
        if top_k:
            for scores in ensemble_scores:
                # Get indices of the top_k results
                top_k_indices = np.argsort(-scores)[:top_k]
                # Get the top_k scores
                top_k_scores = scores[top_k_indices]
                # Combine indices and scores
                top_k_results = np.column_stack((top_k_indices, top_k_scores))
                ensemble_results.append(top_k_results)
        else:
            # Return full results if top_k is not specified
            ensemble_results = ensemble_scores

        return np.array(ensemble_results)