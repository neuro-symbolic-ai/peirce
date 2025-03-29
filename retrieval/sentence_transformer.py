from .abstract import RetrievalModel
from sentence_transformers import SentenceTransformer
from tqdm import tqdm
import numpy as np
from typing import List, Optional


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