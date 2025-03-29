from .abstract import FormalisationModel
from sympy import symbols, Implies, Not, And, Or, Equivalent
from sympy.logic.inference import satisfiable
import sympy
from typing import Optional
from itertools import product
import re


class IsabelleFormaliser(FormalisationModel):

    def __init__(self, llm, prompt_dict: Optional[dict] = None):
        super().__init__(llm, prompt_dict)
        self.llm = llm
        self.logical_form = None
        self.logical_proposition = ''
        self.prompt_dict = prompt_dict

    def _add_quotes(self, isabelle_code: str) -> str:
        assumes_pattern = r'(assumes asm: )(.*)'
        shows_pattern = r'(shows )(.*)'

        def add_quotes_to_line(match):
            content = match.group(2)
            if not content.startswith('"') and not content.endswith('"'):
                content = f'"{content}"'
            return f'{match.group(1)}{content}'
        isabelle_code = re.sub(assumes_pattern,
                               add_quotes_to_line, isabelle_code)
        isabelle_code = re.sub(shows_pattern,
                               add_quotes_to_line, isabelle_code)
        return isabelle_code

    def _fix_assume_quantifier(self, isabelle_code: str) -> str:
        def replace_quantifier(match):
            quantifier_str = match.group(1)
            new_quantifier_str = re.sub(r'[∀∃].*?\.\s', '', quantifier_str)
            return f'assumes asm: "{new_quantifier_str}"'

        assumes_pattern = r'assumes asm: "(.*?)"'
        isabelle_code = re.sub(assumes_pattern, replace_quantifier,
                               isabelle_code)

        return isabelle_code

    def _clean_proof(self, isabelle_code: str) -> str:
        pattern = r'(proof -).*?(qed)(?!.*qed)'
        return re.sub(pattern, r'\1  \n  \n  \n\2',
                      isabelle_code, flags=re.DOTALL)

    def _remove_brackets(self, isabelle_code: str) -> str:
        assumes_pattern = r'(assumes asm: ")(.+)(")'
        shows_pattern = r'(shows ")(.+)(")'
        assumes_match = re.search(assumes_pattern, isabelle_code)
        if assumes_match:
            assumes_content = assumes_match.group(2)
            if '(' in assumes_content and ')' in assumes_content:
                assumes_content = re.sub(r'[\(\),]', ' ', assumes_content)
                isabelle_code = isabelle_code[:assumes_match.start(2)] + assumes_content + isabelle_code[assumes_match.end(2):]
        shows_match = re.search(shows_pattern, isabelle_code)
        if shows_match:
            shows_content = shows_match.group(2)
            if '(' in shows_content and ')' in shows_content:
                shows_content = re.sub(r'[\(\),]', ' ', shows_content)
                isabelle_code = isabelle_code[:shows_match.start(2)] + shows_content + isabelle_code[shows_match.end(2):]
        return isabelle_code

    def _get_parsing(self, premise: str, explanation: str,
                     hypothesis: str) -> str:
        if premise is None:
            premise_sentence = 'none'
        else:
            premise_sentence = premise

        def format_sentences(sentences, type):
            formatted = f"{type}:\n"
            sentence_list = re.split(r'[.\n]\s*', sentences)
            for order, sentence in enumerate(sentence_list, start=1):
                if sentence.strip():
                    formatted += (f"{order}. {sentence.strip()}\n")
            return formatted

        nl_knowledge_base = (
            format_sentences(hypothesis, "Hypothesis Sentence") +
            format_sentences(explanation, "Explanation Sentence") +
            format_sentences(premise_sentence, "Premise Sentence")
        )

        inference_result = self.llm.generate(
            model_prompt_dir='formalisation_model',
            prompt_name=self.prompt_dict['get sentence parse'],
            input_sentence=nl_knowledge_base
        )

        inference_result = re.sub(r'^.*?answer:\s*', '', inference_result,
                                  flags=re.DOTALL | re.IGNORECASE)

        return inference_result

    def _get_davidsonian_form(self, input_sentence: str,
                              premise: str,
                              logical_proposition: str) -> str:

        inference_result = self.llm.generate(
            model_prompt_dir='formalisation_model',
            prompt_name=self.prompt_dict['get davidsonian'],
            input_sentence=input_sentence
        )

        inference_result = '\n'.join([
            line for line in inference_result.split('\n')
            if line and (line.startswith(("Hypothesis", "Explanation",
                                        "Premise", "Logical")) or re.match(r'^\d+\.', line))
        ])

        last_action_index = inference_result.lower().rfind('logical form:')
        if last_action_index != -1:
            action_end_index = inference_result.find('\n', last_action_index)
            if action_end_index != -1:
                inference_result = inference_result[:action_end_index].strip()
        lines = inference_result.split('\n')
        cleaned_lines = [line for line in lines
                         if "Provided sentences" not in line]
        for i in range(len(cleaned_lines) - 1, 0, -1):
            if cleaned_lines[i-1].startswith("Logical"):
                cleaned_lines.insert(i, "")
        
        cleaned_inference_result = '\n'.join(cleaned_lines)
        
        if 'premise sentence' not in cleaned_inference_result.lower():
            cleaned_inference_result += ('\n\nPremise Sentence:\n'
                                         'Logical form: none')

        return cleaned_inference_result

    def _get_axioms(self, davidsonian_form: str) -> str:
        lower_case_result = davidsonian_form.lower()
        start_index = lower_case_result.rfind("explanation sentence")
        if start_index != -1:
            substring_after_explanation = lower_case_result[start_index:]
            end_index_relative = substring_after_explanation.rfind(
                "premise sentence"
            )
            if end_index_relative != -1:
                end_index = start_index + end_index_relative
            else:
                end_index = len(davidsonian_form)
        else:
            end_index = -1
        if start_index != -1 and end_index != -1:
            explanatory_sentences = \
                davidsonian_form[start_index:end_index].strip()
        else:
            explanatory_sentences = ""

        inference_result = self.llm.generate(
            model_prompt_dir='formalisation_model',
            prompt_name=self.prompt_dict['get isabelle axiom'],
            explanatory_sentences=explanatory_sentences
        )

        inference_result = ("imports Main\n\n" +
                            inference_result +
                            "\ntheorem hypothesis:\n assumes asm: \n" +
                            " shows \nproof -\n  \n  \nqed\n\nend")

        return inference_result

    def _get_theorem(self, davidsonian_form: str, axiom: str,
                     premise: str) -> str:
        hypothesis_index = davidsonian_form.lower().rfind("hypothesis")
        if hypothesis_index != -1:
            davidsonian_form = davidsonian_form[hypothesis_index:]
        if premise is not None:
            explanation_pattern = (
                r"(?:Explanation Sentence|Explanation Sentences|"
                r"Explanation sentence|Explanation sentences):"
                r".*?"
                r"(?=Premise Sentence|Premise Sentences|"
                r"Premise sentence|Premise sentences)"
            )
            input_sentence = re.sub(explanation_pattern, '',
                                    davidsonian_form,
                                    flags=re.DOTALL | re.IGNORECASE)
        else:
            explanation_pattern = (
                r"(?:Explanation Sentence|Explanation Sentences|"
                r"Explanation sentence|Explanation sentences).*"
            )
            input_sentence = re.sub(explanation_pattern, '',
                                    davidsonian_form,
                                    flags=re.DOTALL | re.IGNORECASE)

        if premise is not None:
            prompt_file = self.prompt_dict['get isabelle theorem with premise']
        else:
            prompt_file = self.prompt_dict['get isabelle theorem no premise']

        for _ in range(5):
            inference_result = self.llm.generate(
                model_prompt_dir='formalisation_model',
                prompt_name=prompt_file,
                input_sentence=input_sentence,
                axiom_code=axiom
            )

            if "qed" in inference_result and "end" in inference_result:
                inference_result = self._add_quotes(inference_result)
                inference_result = self._fix_assume_quantifier(
                    inference_result
                )
                # inference_result = self._remove_brackets(inference_result)
                return inference_result
        return inference_result

    def _get_logical_proposition(self, explanation: str) -> str:
        def format_sentences(sentences):
            formatted = ''
            sentence_list = re.split(r'[.\n]\s*', sentences)
            for order, sentence in enumerate(sentence_list, start=1):
                if sentence.strip():
                    formatted += (
                        f"Explanatory Sentence {order}: {sentence.strip()}\n"
                        )
            return formatted
        inference_result = self.llm.generate(
            model_prompt_dir='formalisation_model',
            prompt_name=self.prompt_dict['get logical proposition'],
            explanation=format_sentences(explanation)
        )
        # print(inference_result)
        return inference_result

    def _process_logical_proposition(self, logical_proposition: str) -> str:

        def parse_input(input_text):
            lines = input_text.strip().split('\n')
            logical_props = {}
            logical_exprs = []
            mode = None
            for line in lines:
                line = line.strip()
                if not line:
                    continue
                if line.startswith('Logical Propositions:'):
                    mode = 'propositions'
                    continue
                elif line.startswith('Logical Relations:'):
                    mode = 'relations'
                    continue
                else:
                    if mode == 'propositions':
                        if ':' in line:
                            key, value = line.split(':', 1)
                            value = value.strip()
                            logical_props[key.strip()] = value
                    elif mode == 'relations':
                        if '#' in line:
                            expr, comment = line.split('#', 1)
                        else:
                            expr = line
                        expr = expr.strip()
                        if expr:  
                            logical_exprs.append(expr)
            return logical_props, logical_exprs

        logical_props, logical_exprs = parse_input(logical_proposition)
        
        if not logical_exprs or all(not expr for expr in logical_exprs):
            result = 'Logical Propositions:\n'
            for key, value in logical_props.items():
                result += f'{key}: {value}\n'
            result += '\nLogical Relations:\nNone logical relations'
            return result

        symbols_dict = {}
        symbol_meanings = {}
        sanitized_symbol_names = {}

        for key, value in logical_props.items():
            value_no_parentheses = re.sub(r'\(.*?\)', '', value).strip()
            key_sanitized = re.sub(r'\W|^(?=\d)', '_', key)
            sanitized_symbol_names[key] = key_sanitized
            sym = symbols(key_sanitized)
            symbols_dict[key_sanitized] = sym
            symbol_meanings[sym] = value_no_parentheses  

        propositions = []
        initial_implications_set = set()

        for expr in logical_exprs:
            if not expr:  
                continue
            expr_replaced = expr
            for original_key, sanitized_key in sanitized_symbol_names.items():
                pattern = r'\b{}\b'.format(re.escape(original_key))
                expr_replaced = re.sub(pattern, sanitized_key, expr_replaced)
            local_dict = {
                **symbols_dict,
                "Not": Not,
                "And": And,
                "Or": Or,
                "Implies": Implies,
                "Equivalent": Equivalent,
            }
            try:
                proposition = eval(expr_replaced, {"__builtins__": {}}, local_dict)
                if proposition is not None:  
                    propositions.append(proposition)
                    proposition = sympy.simplify(proposition)
                    initial_implications_set.add(proposition)
            except Exception as e:
                continue  

        derived_implications = set()

        def is_equivalent(expr1, expr2):
            return not satisfiable(Not(Equivalent(expr1, expr2)))

        def is_entailed(propositions, conclusion):
            premises = And(*propositions)
            formula = Implies(premises, conclusion)
            return not satisfiable(Not(formula))

        logical_atoms = set()
        for prop in propositions:
            logical_atoms.update(prop.atoms())

        all_literals = set()
        for atom in logical_atoms:
            all_literals.add(atom)
            all_literals.add(Not(atom))

        possible_pairs = product(all_literals, repeat=2)

        for antecedent, consequent in possible_pairs:
            if antecedent == consequent:
                continue  
            conclusion = Implies(antecedent, consequent)
            if any(is_equivalent(conclusion, imp) for imp in initial_implications_set):
                continue  
            if is_entailed(propositions, conclusion):
                derived_implications.add(conclusion)

        def expr_to_meaning(expr):
            if isinstance(expr, sympy.Symbol):
                return symbol_meanings.get(expr, str(expr))
            elif expr.func == Not:
                return f'Not({expr_to_meaning(expr.args[0])})'
            elif expr.func == Implies:
                return f'Implies({expr_to_meaning(expr.args[0])}, {expr_to_meaning(expr.args[1])})'
            elif expr.func == Equivalent:
                return f'Equivalent({expr_to_meaning(expr.args[0])}, {expr_to_meaning(expr.args[1])})'
            else:
                return str(expr)

        def implication_expr_to_str(expr):
            if expr.func == Not:
                arg = implication_expr_to_str(expr.args[0])
                return f'Not({arg})'
            elif expr.func == Implies:
                ant = implication_expr_to_str(expr.args[0])
                con = implication_expr_to_str(expr.args[1])
                return f'Implies({ant}, {con})'
            elif expr.func == Equivalent:
                ant = implication_expr_to_str(expr.args[0])
                con = implication_expr_to_str(expr.args[1])
                return f'Equivalent({ant}, {con})'
            elif isinstance(expr, sympy.Symbol):
                for original_key, sanitized_key in sanitized_symbol_names.items():
                    if str(expr) == sanitized_key:
                        return original_key
                return str(expr)
            else:
                return str(expr)

        result = ''

        result += 'Logical Propositions:\n'
        for key, meaning in logical_props.items():
            result += f'{key}: {meaning}\n'

        result += '\nLogical Relations:\n'
        for prop_expr, prop in zip(logical_exprs, propositions):
            prop_meaning = expr_to_meaning(prop)
            result += f'{prop_expr}\n{prop_meaning}\n--------\n'

        result += '\nDerived Implications:\n'
        for implication in derived_implications:
            implication_str = implication_expr_to_str(implication)
            implication_meaning = expr_to_meaning(implication)
            result += f'{implication_str}\n{implication_meaning}\n--------\n'

        return result

    def get_isabelle_proof(self, premise: str, explanation: str,
                           hypothesis: str, isabelle_code: str) -> str:
        logical_proposition = self.logical_proposition
        logical_information = self._process_logical_proposition(logical_proposition)
        lines = isabelle_code.split('\n')
        known_information = ""
        try_to_prove = ""
        for line in lines:
            if line.strip().startswith("assumes asm:"):
                known_information = line.split('"')[1]
            elif line.strip().startswith("shows"):
                try_to_prove = line.split('"')[1]
        # print(derived_rules)
        for _ in range(5):
            inference_result = self.llm.generate(
                model_prompt_dir='formalisation_model',
                prompt_name=self.prompt_dict['get isabelle proof'],
                premise=premise,
                explanation=explanation,
                hypothesis=hypothesis,
                isabelle_code=isabelle_code,
                known_information=known_information,
                try_to_prove=try_to_prove,
                logical_information=logical_information
            )
            if 'proof -' in inference_result and 'qed' in inference_result:
                proof_content_pattern = r'proof -.*?qed'
                match = re.search(proof_content_pattern, inference_result,
                                  re.DOTALL)
                if match:
                    inference_result = match.group(0)
                    lines = inference_result.split('\n')
                    modified_lines = []
                    for line in lines:
                        if 'using' in line and '(*' not in line:
                            modi_line = re.sub(r'(.*)\s+using\s+.*?(?=\s*$)',
                                               r'\1 <ATP>',
                                               line, flags=re.DOTALL)
                            modified_lines.append(modi_line)
                        else:
                            modified_lines.append(line)
                    inference_result = '\n'.join(modified_lines)
                    proof_pattern = r'proof -.*?qed'
                    isabelle_code = re.sub(proof_pattern, inference_result,
                                           isabelle_code, flags=re.DOTALL)
                    isabelle_code = self._fix_assume_quantifier(isabelle_code)
                return isabelle_code, logical_information
        return isabelle_code, logical_information

    def get_logical_form(self, premise: str, explanation: str,
                         hypothesis: str, logical_form: str) -> str:
        inference_result = self.llm.generate(
            model_prompt_dir='formalisation_model',
            prompt_name=self.prompt_dict['get logical form'],
            premise=premise,
            explanation=explanation,
            hypothesis=hypothesis,
            logical_form=logical_form
        )
        return inference_result

    def get_unused_explanations(self) -> list[str]:
        isabelle_code = self.code
        proof_pattern = r'proof -.*?qed'
        match = re.search(proof_pattern, isabelle_code, re.DOTALL)
        if match:
            proof_code = match.group(0)
        else:
            proof_code = ''
        explanation_matches = re.findall(r'explanation_\d+', proof_code)
        used_explanations = '\n'.join(explanation_matches)
        collected_explanations = used_explanations.split('\n')
        all_explanations = set(re.findall(r"(explanation_\d+)", isabelle_code))
        unused_explanations = [exp for exp in all_explanations if
                               exp not in collected_explanations]

        return unused_explanations

    def fix_inner_syntax_error(self, isabelle_code: str,
                               error_detail: str, inner_code: str) -> str:
        refined_code = self.llm.generate(
            model_prompt_dir='formalisation_model',
            prompt_name=self.prompt_dict['refine inner syntax error'],
            code=isabelle_code,
            error_detail=error_detail,
            code_cause_error=inner_code
        )
        refined_code = self._clean_proof(refined_code)
        refined_code = self._add_quotes(refined_code)
        refined_code = self._fix_assume_quantifier(refined_code)
        return refined_code

    def fix_contradiction_error(self, isabelle_code: str,
                                contradiction_code: str) -> str:
        refined_code = self.llm.generate(
            model_prompt_dir='formalisation_model',
            prompt_name=self.prompt_dict['refine contradiction'],
            natural_language=self.logical_form,
            code=isabelle_code,
            code_cause_error=contradiction_code
        )
        refined_code = self._clean_proof(refined_code)
        refined_code = self._add_quotes(refined_code)
        refined_code = self._fix_assume_quantifier(refined_code)
        return refined_code

    def formalise(self, theory_name: str, premise: str,
                  explanation: str, hypothesis: str,
                  logical_form: str = 'event-based semantics') -> str:
        if logical_form == 'event-based semantics':
            syntactic_parsed_structure = self._get_parsing(
                premise,
                explanation,
                hypothesis
            )
            self.logical_proposition = self._get_logical_proposition(explanation)
            davidsonian_form = self._get_davidsonian_form(
                syntactic_parsed_structure,
                premise,
                self.logical_proposition
            )
            # print(syntactic_parsed_structure)
            print("\n------------------ 1) Syntactic Parsing ------------------")
            print(f"\n{syntactic_parsed_structure}")
            print("\n------------------ 2) Neodavidsonian From ------------------")
            print(f"\n{davidsonian_form}")
            axioms = self._get_axioms(davidsonian_form)
            theorem = self._get_theorem(davidsonian_form, axioms, premise)
            self.code = f'theory {theory_name}\n' + theorem
            self.code = self._clean_proof(self.code)
            self.save_formalised_kb(self.code, theory_name)
            self.logical_form = davidsonian_form
        return self.code

    def save_formalised_kb(self, isabelle_code: str, theory_name: str) -> None:
        isabelle_code = re.sub(r'.*imports Main', 'imports Main',
                               isabelle_code, flags=re.DOTALL)
        isabelle_code = f'theory {theory_name}\n' + isabelle_code
        self.code = isabelle_code
        with open(f'formalisation/isabelle/{theory_name}.thy', 'w') as f:
            f.write(isabelle_code)

