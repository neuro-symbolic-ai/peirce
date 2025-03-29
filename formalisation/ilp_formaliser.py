from .abstract import FormalisationModel
from typing import Optional


class ILPFormaliser(FormalisationModel):
    def __init__(self, llm, prompt_dict: Optional[dict] = None):
        super().__init__(llm, prompt_dict)
        self.llm = llm
        self.prompt_dict = prompt_dict

    def _get_induced_prolog_theory(self, background_knowledge: str,
                                   pos_neg_examples: str) -> str:
        induced_prolog_theory = self.llm.generate(
            model_prompt_dir='formalisation_model',
            prompt_name=self.prompt_dict['get prolog theory'],
            background_knowledge=background_knowledge,
            positive_and_negative_examples=pos_neg_examples,
        )
        return induced_prolog_theory

    def formalise(self, background_knowledge: str,
                  pos_neg_examples: str) -> str:
        induced_prolog_theory = self._get_induced_prolog_theory(
            background_knowledge,
            pos_neg_examples
        )
        return induced_prolog_theory

    def save_formalised_kb(self, theory_code: str, theory_name: str) -> None:
        lines = theory_code.split('\n')
        filtered_lines = [line for line in lines if line.strip() != 'prolog' and not line.strip().startswith('%')]
        theory_code = '\n'.join(filtered_lines)
        with open(f'formalisation/prolog/{theory_name}/theory.pl', 'w') as f:
            f.write(theory_code)