from abc import ABC, abstractmethod
from sklearn.metrics import average_precision_score
import numpy as np
from tqdm import tqdm

class EvaluationModel(ABC):
    """
    Abstract base class for evaluation models.
    """

    def __init__(self, gold_references):
        """
        Initializes the EvaluationModel.

        :param gold_references: List of gold references (ground truth) for evaluation.
        """
        self.gold_references = gold_references

    @abstractmethod
    def evaluate(self, *args, **kwargs):
        """
        Abstract method to evaluate predictions against gold references.
        """
        pass
    

class ExplanationRetrievalEvaluation(EvaluationModel):
    """
    Evaluation model for explanation retrieval, computing mean average precision (MAP).
    """

    def __init__(self, gold_references):
        """
        Initializes the ExplanationRetrievalEvaluation.

        :param gold_references: List of gold references (ground truth) for evaluation.
        """
        super().__init__(gold_references)
        self._pre_process()

    def _pre_process(self):
        """
        Preprocess the gold references to extract premise IDs for each hypothesis.
        """
        self.premises_list = []
        for hypothesis in self.gold_references:
            # Extract IDs of all premises for the current hypothesis
            self.premises_list.append({premise.id for premise in hypothesis.premises})

    def evaluate(self, predictions, facts_kb):
        """
        Evaluate predictions by computing mean average precision (MAP).

        :param predictions: List of predictions where each entry is a list of scores.
        :param facts_kb: List of facts (or premises) with IDs.
        :return: Dictionary with MAP score.
        """
        # Map predictions to ids in facts_kb
        mapped_predictions = []
        facts_dict = {fact.id: index for index, fact in enumerate(facts_kb)}
        
        for res in tqdm(predictions, desc="Processing predictions"):
            # Map scores to the ids of the premises/facts
            predictions_ids = [(fact.id, res[facts_dict[fact.id]]) for fact in facts_kb]
            mapped_predictions.append(predictions_ids)

        # Compute MAP score for each hypothesis
        eval_scores = {"map": []}
        
        for hypothesis_index, hypothesis in tqdm(enumerate(mapped_predictions), desc="Processing evaluation", total=len(mapped_predictions)):
            y_scores = []
            y_true = []

            # Collect scores and true labels
            for fact_id, score in hypothesis:
                y_scores.append(score)
                y_true.append(1 if fact_id in self.premises_list[hypothesis_index] else 0)
            
            # Convert lists to numpy arrays for evaluation
            y_scores = np.array(y_scores)
            y_true = np.array(y_true)
            
            # Compute average precision for the current hypothesis
            eval_scores["map"].append(average_precision_score(y_true, y_scores))
        
        # Compute mean average precision across all hypotheses
        eval_scores["map"] = np.mean(eval_scores["map"])
        return eval_scores
