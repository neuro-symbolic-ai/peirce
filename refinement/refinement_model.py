from typing import Optional
from pathlib import Path
import logging


class RefinementModel():
    def __init__(self, generative_model, critique_models, critique_mode,
                 prompt_dict: Optional[dict] = None):
        self.generative_model = generative_model
        self.critique_mode = critique_mode
        self.critique_models_list = critique_models[self.critique_mode]
        if self.critique_mode == 'hard':
            self.critique_model = critique_models['hard'][0]
        self.logger = None
        self.prompt_dict = prompt_dict

    # setup logger
    def _setup_logger(self, data_name: str):
        log_dir = Path(f'logs/{data_name}')
        log_dir.mkdir(parents=True, exist_ok=True)
        logger = logging.getLogger(data_name)
        logger.setLevel(logging.INFO)

        file_handler = logging.FileHandler(log_dir / 'refinement.log')
        file_formatter = logging.Formatter('%(message)s')
        file_handler.setFormatter(file_formatter)
        logger.addHandler(file_handler)

        console_handler = logging.StreamHandler()
        console_handler.setFormatter(file_formatter)
        logger.addHandler(console_handler)

        return logger

    # use generative_model to generate explanaiton
    def _get_explanation(self, hypothesis: str,
                         premise: Optional[str] = None) -> str:
        premise_sentence = ('' if premise is None else
                            f'Provided Premise Sentence:\n{premise}\n')
        explanation = ''
        explanation = self.generative_model.generate(
            model_prompt_dir='refinement_model',
            prompt_name=self.prompt_dict['generate explanation'],
            hypothesis_sentence=hypothesis,
            premise_sentence=premise_sentence
        )
        return explanation

    def _refine_explanation(self, explanation: str,
                            hypothesis: str,
                            critique_output: Optional[dict] = None,
                            premise: Optional[str] = None) -> str:
        refined_explanations = ''
        if self.critique_mode == 'hard':
            if premise is not None:
                refined_explanations = self.generative_model.generate(
                    model_prompt_dir='refinement_model',
                    prompt_name=self.prompt_dict['refine with premise'],
                    explanation=explanation,
                    hypothesis=hypothesis,
                    logical_information=f'{critique_output["logical information"]}',
                    critique_output=f'Code:\n{critique_output["code"]}\n\nProof step that failed:\n{critique_output["error code"]}',
                    premise=f'Original premise sentence:\n{premise}',
                    prefix='explanatory sentences:',
                    test=True,
                    numbered_list=True,
                    remove_number=True
                )
            else:
                refined_explanations = self.generative_model.generate(
                    model_prompt_dir='refinement_model',
                    prompt_name=self.prompt_dict['refine no premise'],
                    explanation=explanation,
                    hypothesis=hypothesis,
                    logical_information=f'{critique_output["logical information"]}',
                    critique_output=f'Code:\n{critique_output["code"]}\n\nProof step that failed:\n{critique_output["error code"]}',
                    prefix='explanatory sentences:',
                    test=True,
                    numbered_list=True,
                    remove_number=True
                )
        elif self.critique_mode == 'soft':
            if premise is not None:
                refined_explanations = self.generative_model.generate(
                    model_prompt_dir='refinement_model',
                    prompt_name=self.prompt_dict['refine with premise'],
                    explanation=explanation,
                    hypothesis=hypothesis,
                    premise=premise,
                    critique_output=f'{critique_output}',
                    prefix='explanatory sentences:',
                    test=True,
                    numbered_list=False,
                    remove_number=False
                )
            else:
                refined_explanations = self.generative_model.generate(
                    model_prompt_dir='refinement_model',
                    prompt_name=self.prompt_dict['refine no premise'],
                    explanation=explanation,
                    hypothesis=hypothesis,
                    critique_output=f'{critique_output}',
                    prefix='explanatory sentences:',
                    test=True,
                    numbered_list=False,
                    remove_number=False
                )

        return refined_explanations

    def refine(self, hypothesis: str, premise: Optional[str] = None,
               explanation: Optional[str] = None,
               data_name: str = 'example',
               iterations: int = 11) -> dict:

        # if premise or explanation is empty, set it to None
        premise = None if premise is None or premise.strip() == '' else premise
        explanation = (None if explanation is None or
                       explanation.strip() == '' else explanation)
        # if explanation is None, use generative_model to generate explanation
        if explanation is None:
            explanation = self._get_explanation(hypothesis, premise)

        history_explanation = []
        history_critique_output = []
        result = {}

        for i in range(iterations):
            all_critique_output = []
            # start isabelle server
            print(f"\n================= Iteration Number {i} ==================\n")
            print(f"Premise: {premise}")
            print(f"Hypothesis: {hypothesis}")
            print(f"Explanation: ")
            for k, sentence in enumerate(explanation.split('.'), 1):
                if sentence.strip():
                    print((f"{k}. {sentence.strip()}"))
            to_append_explanation = f'{i} iteration: {explanation}'
            history_explanation.append(to_append_explanation)
            print("\n-------------- Verification and Refinement -------------------")
            if self.critique_mode == 'hard':
                critique_output = self.critique_model.critique(
                    iteration_number=i,
                    explanation=explanation,
                    hypothesis=hypothesis,
                    premise=premise
                )
                history_critique_output.append(f'{i} iteration: {critique_output}')
            else:
                for model in self.critique_models_list:
                    critique_output = model.critique(
                        premise=premise,
                        hypothesis=hypothesis,
                        explanation=explanation
                    )
                    print(f'{i} iteration: {critique_output}')
                    all_critique_output.append(critique_output)
                history_critique_output.append(f'{i} iteration: {all_critique_output}')
            print("\n-------------- 4) Results -------------------\n")
            # if the critique model is a hard critique model
            if self.critique_mode == 'hard':
                if not critique_output['syntactic validity']:
                    print("\nSyntacitc error found in the formalization!! Go to the next iteration...\n")
                    if i == iterations - 1:
                        print(f'The explanation is not valid after {iterations} iterations')
                        result = {
                            'semantic validity': critique_output['semantic validity'],
                            'premise': premise,
                            'hypothesis': hypothesis,
                            'history explanation': history_explanation,
                            'history critique output': history_critique_output
                        }
                    continue

                if critique_output['semantic validity']:
                    print("The explanation is logically valid!")
                    result = {
                        'semantic validity': critique_output['semantic validity'],
                        'premise': premise,
                        'hypothesis': hypothesis,
                        'refined explanation': explanation,
                        'refined iteration': i,
                        'history explanation': history_explanation,
                        'history critique output': history_critique_output
                    }
                    break
                else:
                    # if the explanation is not valid, refine the explanation
                    print("No proof can be found!The explanation is not logically valid! Refinement...")
                    print("\n-------------- 5) Refinement Feedback -------------------\n")
                    if 'error code' in critique_output:
                        print(f'Error:\n{critique_output["error code"]}')
                    else:
                        critique_output['error code'] = ''
                    print(f'\nLogical information:\n{critique_output["logical information"]}')
                    explanation = self._refine_explanation(
                        explanation, hypothesis,
                        critique_output, premise,
                    )
                    print('\n-------------- 6) Refined Explanation -------------------\n')
                    for j, sentence in enumerate(explanation.split('.'), 1):
                        if sentence.strip():
                            print(f"{j}. {sentence.strip()}")
                    if i == iterations - 1:
                        print(f'The explanation is not valid after {iterations} iterations')
                        result = {
                            'semantic validity': critique_output['semantic validity'],
                            'premise': premise,
                            'hypothesis': hypothesis,
                            'history explanation': history_explanation,
                            'history critique output': history_critique_output
                        }
            elif self.critique_mode == 'soft':
                print(f'{i} iteration: {all_critique_output}')
                print("\n-------------- 5) Refinement Feedback -------------------\n")
                explanation = self._refine_explanation(
                    explanation, hypothesis,
                    all_critique_output, premise,
                )
                print('\n-------------- 6) Refined Explanation -------------------\n')
                for sentence in explanation.split('.'):
                    if sentence.strip():
                        print(f"{sentence.strip()}")
                if i == iterations - 1:
                    result = {
                        'premise': premise,
                        'hypothesis': hypothesis,
                        'history explanation': history_explanation,
                        'history critique output': history_critique_output
                    }

            print("=====================================================")
            
        print(result)
        return result
