from .abstract import CritiqueModel
from formalisation.ilp_formaliser import ILPFormaliser
from typing import Optional
from pyswip import Prolog


class ILPSolver(CritiqueModel):
    def __init__(self, generative_model,
                 theory_name: Optional[str] = 'example',
                 prompt_dict: Optional[dict] = None):
        super().__init__(generative_model,
                         prompt_dict,
                         type='hard')
        if prompt_dict is None:
            prompt_dict = {
                'get prolog theory':
                    'get_prolog_theory_prompt.txt',
            }
        self.prolog = Prolog()
        self.theory_name = theory_name
        self.prompt_dict = prompt_dict
        self.background_knowledge_path = f'./formalisation/prolog/{theory_name}/bk.pl'
        self.pos_neg_examples_path = f'./formalisation/prolog/{theory_name}/exs.pl'
        self.theory_path = f'./formalisation/prolog/{theory_name}/theory.pl'
        self.formaliser = ILPFormaliser(generative_model, prompt_dict)

    def _get_prolog_theory(self):
        with open(f'{self.background_knowledge_path}', 'r') as file:
            background_knowledge = file.read()
        with open(f'{self.pos_neg_examples_path}', 'r') as file:
            pos_neg_examples = file.read()
        theory = self.formaliser.formalise(
            background_knowledge,
            pos_neg_examples,
        )
        self.formaliser.save_formalised_kb(theory, self.theory_name)
        return theory

    def critique(self) -> dict:
        theory = self._get_prolog_theory()
        critique_output = {}
        tp = 0
        fp = 0
        fn = 0
        tn = 0

        wrong_examples = {
            'false_positives': [],  # false positives
            'false_negatives': []   # false negatives
        }

        pos_examples = []
        neg_examples = []
        with open(f'{self.pos_neg_examples_path}', 'r') as file:
            for line in file:
                line = line.strip()
                if line.startswith('pos(') and line.endswith(').'):
                    example = line[4:-2]
                    pos_examples.append(example)
                elif line.startswith('neg(') and line.endswith(').'):
                    example = line[4:-2]
                    neg_examples.append(example)

        with open(f'{self.background_knowledge_path}', 'r') as file:
            background_knowledge = file.read()

        with open(f'{self.theory_path}', 'r') as file:
            theory_lines = file.readlines()

        for fact in background_knowledge.split('\n'):
            fact = fact.strip()
            if fact and not fact.startswith('%'):
                if fact.endswith('.'):
                    fact = fact[:-1]
                self.prolog.assertz(fact)

        for rule in theory_lines:
            rule = rule.strip()
            if rule and not rule.startswith('%'):
                if rule.endswith('.'):
                    rule = rule[:-1]
                self.prolog.assertz(rule)

        # query positive examples
        for example in pos_examples:
            result = list(self.prolog.query(example))
            if result:
                tp += 1  # positive example is correctly derived
            else:
                fn += 1  # positive example is not derived
                wrong_examples['false_negatives'].append(example)

        # query negative examples
        for example in neg_examples:
            result = list(self.prolog.query(example))
            if result:
                fp += 1  # negative example is incorrectly derived
                wrong_examples['false_positives'].append(example)
            else:
                tn += 1  # negative example is correctly not derived

        precision = tp / (tp + fp) if (tp + fp) > 0 else 0
        recall = tp / (tp + fn) if (tp + fn) > 0 else 0
        f1 = 2 * precision * recall / (precision + recall) if (precision + recall) > 0 else 0
        accuracy = (tp + tn) / (tp + tn + fp + fn) if (tp + tn + fp + fn) > 0 else 0

        critique_output['tp'] = tp
        critique_output['fp'] = fp
        critique_output['fn'] = fn
        critique_output['tn'] = tn
        critique_output['precision'] = precision
        critique_output['recall'] = recall
        critique_output['f1'] = f1
        critique_output['accuracy'] = accuracy
        critique_output['generated_theory'] = theory
        critique_output['wrong_examples'] = wrong_examples

        return critique_output

    def shutdown(self):
        pass
