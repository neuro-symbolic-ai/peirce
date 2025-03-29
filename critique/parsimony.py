from .abstract import CritiqueModel

import re  
import spacy
from typing import List

from transformers.utils import logging
logging.set_verbosity_error() 

class ParsimonyCritique(CritiqueModel):

    def __init__(self):
        super().__init__(generative_model=None, prompt_dict=None, type="soft")
        self.spacy_model = spacy.load("en_core_web_sm")

    def shutdown(self, *args, **kwargs):
        pass

    def parse_explanation(self, exp: str):
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

    def extract_unique_concepts(self, text: str) -> List[str]:
        doc = self.spacy_model(text)
        nouns_adjectives = [token.text for token in doc if token.pos_ in ['NOUN', 'ADJ']]
        return list(set(nouns_adjectives))

    def critique(self, premise: str, hypothesis: str, explanation: str) -> dict:
        
        # 1. Extract steps from explanation
        steps = self.parse_explanation(explanation)["steps"]
        
        # 2. Extract unique concepts from hypothesis and conclusion
        premise_sent = f"{premise} {hypothesis}"
        premise_concepts = self.extract_unique_concepts(premise_sent)

        # 3. Extract unique concepts from explanation
        expl_sent = " ".join(steps)
        expl_concepts = self.extract_unique_concepts(expl_sent)

        # Calculate semantic drift as set difference
        drift = len(set(expl_concepts).difference(set(premise_concepts)))
        
        critique_output = {}
        critique_output['parsimony'] = drift
        return critique_output
