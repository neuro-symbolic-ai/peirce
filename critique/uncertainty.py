from .abstract import CritiqueModel
from certainty_estimator.predict_certainty import CertaintyEstimator
import torch
import numpy as np
import re 
from typing import Optional
class UncertaintyCritique(CritiqueModel):
      
    def __init__(self):
        super().__init__(generative_model=None, prompt_dict=None, type="soft")
        self.use_cuda = True if torch.cuda.is_available() else False
        self.estimator = CertaintyEstimator('sentence-level', cuda=self.use_cuda)

    def shutdown(self, *args, **kwargs):
        pass

    def parse_explanation(self, exp: str) -> dict:
            step_pattern = r"(Step \d+:.*?(?=\n))"
            assumption_pattern = r"(Assumption:.*?(?=\n))"

            # Extract steps and assumptions
            steps = re.findall(step_pattern, exp, re.DOTALL)
            assumptions = re.findall(assumption_pattern, exp, re.DOTALL)

            steps = [step.split(":")[1].strip() for step in steps]
            assumptions = [assumption.split(":")[1].strip() for assumption in assumptions]

            summary_match = re.search(r'Therefore,.*', exp)
            summary = summary_match.group(0) if summary_match else steps[-1]
            
            return {"steps": steps, "assumptions": assumptions, "summary": summary}


    def calculate_avg_uncertainity(self, texts: list) -> float:
        """
        Certainty estimator returns score between 1 and 6, with 6 being the highest certainty.
        To retrieve uncertainty, we need to subtract the certainty score from the max score 6.
        """
        return np.mean([ 6 - score for score in self.estimator.predict(texts)])

    def critique(self, premise: Optional[str] = None, hypothesis: Optional[str] = None, explanation: str = "") -> dict:
         # 1. parse explanation
         exp_dict = self.parse_explanation(explanation)

         # 2. Calculate uncertainty over extracted assumptions 
         assumption_uncertainty = self.calculate_avg_uncertainity(exp_dict["assumptions"])

         # 3. Calculate uncertainty over summary 
         summary_uncertainty = self.calculate_avg_uncertainity([exp_dict["summary"]])
         
         critique_output = {}
         critique_output['uncertainty'] = (assumption_uncertainty + summary_uncertainty) / 2
         return critique_output