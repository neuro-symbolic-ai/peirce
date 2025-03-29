from .abstract import CritiqueModel
from isabelle_client import start_isabelle_server, get_isabelle_client
from formalisation.isabelle_formaliser import IsabelleFormaliser
from typing import Optional
import threading
import time
import json
import re
import yaml


class IsabelleCritique(CritiqueModel):
    def __init__(self, generative_model, isabelle_session,
                 theory_name: Optional[str] = 'example',
                 prompt_dict: Optional[dict] = None):
        super().__init__(generative_model,
                         prompt_dict,
                         type='hard')
        if prompt_dict is None:
            prompt_dict = {
                'get davidsonian':
                    'get_davidsonian_form_prompt.txt',
                'get isabelle axiom': 'get_isabelle_axiom_prompt.txt',
                'get isabelle theorem no premise':
                    'get_isabelle_theorem_no_premise_prompt.txt',
                'get isabelle theorem with premise':
                    'get_isabelle_theorem_with_premise_prompt.txt',
                'refine contradiction':
                    'refine_contradiction_syntax_error_prompt.txt',
                'refine inner syntax error':
                    'refine_inner_syntax_error_prompt.txt',
                'get isabelle proof': 'get_isabelle_proof_prompt.txt',
                'get sentence parse': 'get_sentence_parse_prompt.txt',
                'refine davidsonian form': 'refine_davidsonian_form_prompt.txt',
                'get logical proposition': 'get_logical_proposition_prompt.txt'
            }
        self.isabelle_name = 'test'
        self.port = 7777
        self.log_file = 'server.log'
        self.session_name = isabelle_session
        self.dirs = '../../Isabelle2023'
        self.verbose = True
        self.options = None
        self.watchdog_timeout = 60 #150
        self._init_client()
        self._init_session()
        self.code = None
        self.theory_name = theory_name
        self.prompt_dict = prompt_dict
        self.formaliser = IsabelleFormaliser(generative_model, prompt_dict)
        self.isabelle_dir = self._get_isabelle_dir()

    # get the path which saves isabelle theories
    def _get_isabelle_dir(self):
        with open('config.yaml', 'r') as file:
            config = yaml.safe_load(file)
        return config['isabelle']['master_dir']

    # init isabelle server
    def _init_client(self):
        server_info, _ = start_isabelle_server(
            name="test", port=self.port, log_file=self.log_file
        )
        self.isabelle = get_isabelle_client(server_info)

    # init isabelle session (HOL, ZF, HOL-Proof, ...)
    def _init_session(self):
        self.isabelle.session_build(
            session=self.session_name, dirs=self.dirs,
            verbose=self.verbose, options=self.options
        )
        self.start_id = self.isabelle.session_start(session=self.session_name)

    # get isabelle response
    def _get_response(self, theories, master_dir):
        start_time = time.time()
        isabelle_response = self.isabelle.use_theories(
            session_id=self.start_id,
            theories=theories,
            master_dir=master_dir,
            watchdog_timeout=self.watchdog_timeout
        )
        solving_time = time.time() - start_time
        return isabelle_response, solving_time

    def _get_formalisation(self, explanation: str,
                           hypothesis: str,
                           premise: Optional[str],
                           theory_name: Optional[str]):
        # get isabelle code from input natural language sentences
        self.code = self.formaliser.formalise(
            theory_name, premise,
            explanation, hypothesis,
            logical_form='event-based semantics',
        )

    def _get_isabelle_syntax_output(self, theory_name: str,
                                    explanation: str,
                                    hypothesis: str,
                                    premise: Optional[str] = None) -> bool:
        # formalise the nl into isabelle theory
        self._get_formalisation(
            explanation=explanation,
            hypothesis=hypothesis,
            premise=premise,
            theory_name=theory_name
        )
        has_syntax_error = True
        # check and refine any syntatic errors in the code
        for i in range(5):
            has_inner_syntax_error = False
            has_contradiction_error = False
            error_detail = []
            inner_code = ''
            contradiction_code = ''
            inference_time = 9999
            # check inner and contradiction error
            (has_inner_syntax_error,
             has_contradiction_error,
             error_detail,
             inner_code,
             contradiction_code,
             inference_time
             ) = self.check_syntax_error(theory_name, self.isabelle_dir,
                                         self.code)
            # if has inner syntax error, refine it
            if has_inner_syntax_error:
                refined_code = self.formaliser.fix_inner_syntax_error(
                    self.code, error_detail, inner_code
                )
                self.formaliser.save_formalised_kb(refined_code,
                                                   theory_name)
                self.code = self.formaliser.code
                continue
            # if has contradition syntax error, refine it
            if has_contradiction_error:
                refined_code = self.formaliser.fix_contradiction_error(
                    self.code, contradiction_code
                )
                self.formaliser.save_formalised_kb(refined_code,
                                                   theory_name)
                self.code = self.formaliser.code
                continue
            if not has_inner_syntax_error and not has_contradiction_error:
                has_syntax_error = False
                break
            else:
                continue
        self.code, logical_information = self.formaliser.get_isabelle_proof(
            premise,
            explanation,
            hypothesis,
            self.code
        )
        print("\n------------------ 3) Isabelle Code ------------------")
        print(f"\n{self.code}")
        self.formaliser.save_formalised_kb(self.code,
                                           theory_name)
        return has_syntax_error, logical_information

    # using isabelle client to call isabelle to check
    def check_syntax_error(self, theory_name, master_dir, isabelle_code):
        isa_code_lines = isabelle_code.split('\n')
        for i, line in enumerate(isa_code_lines):
            if line.strip().startswith('shows'):
                start = line.index('"')
                end = line.rindex('"')
                isa_code_lines[i] = line[:start] + 'False' + line[end+1:]
                break
        check_syntax_error_code = '\n'.join(isa_code_lines)
        pattern = r'(proof -).*?(qed)(?!.*qed)'
        check_syntax_error_code = re.sub(pattern, r'  sledgehammer\n  oops',
                                         check_syntax_error_code,
                                         flags=re.DOTALL)
        with open(f'formalisation/isabelle/{theory_name}.thy', 'w') as f:
            f.write(check_syntax_error_code)

        theories_name = [theory_name]
        isabelle_response, solving_time = \
            self._get_response(theories_name, master_dir)
        has_inner_syntax_error = False
        has_contradiction_error = False
        error_details = []
        lines = []
        inner_code = ''
        error_code_detail = []
        tactic_list = []
        tactic_messages = []
        contradiction_code = ''
        explanations = []
        found_explanations = {}
        finished_response = next((item for item in isabelle_response
                                  if item.response_type == 'FINISHED'), None)
        # Error Keywords
        error_keywords = ["Type unification failed", "Inner lexical error",
                          "Outer syntax error", "Inner syntax error",
                          "Outer lexical error", "Malformed command syntax",
                          "Undefined type name"]
        # Warning Keywords
        warning_keywords = ["Introduced fixed type variable"]
        if finished_response is not None:
            response_body = json.loads(finished_response.response_body)
            # Handling errors
            if response_body.get('errors'):
                for error in response_body['errors']:
                    message = error['message']
                    position = error['pos']
                    line = position['line']
                    if any(keyword in message for keyword in error_keywords):
                        error_details.append(
                            f"Error on line {line}: {message}"
                        )
                        lines.append(line)
                        has_inner_syntax_error = True
            else:
                has_inner_syntax_error = False

            for node in response_body.get('nodes', []):
                for message in node.get('messages', []):
                    tactic_messages.append(message['message'])

            if all("no proof found" not in item.lower()
                   for item in tactic_messages):
                tactic_list = [item for item in tactic_messages
                               if "try this:" in item.lower()]
                for item in tactic_list:
                    matches = re.findall(r'explanation_\d+', item)
                    explanations.extend(matches)
                explanations = sorted(set(explanations),
                                      key=lambda x: int(x.split('_')[1]))
                isabelle_code_lines = isabelle_code.split('\n')
                found_explanations = {}
                for line in isabelle_code_lines:
                    for exp in explanations:
                        if exp in line:
                            found_explanations[exp] = line.strip()
                if explanations != [] and found_explanations != {}:
                    contradiction_code = \
                        '\n\n'.join(found_explanations.values())
                has_contradiction_error = True
            else:
                has_contradiction_error = False

            # Handling warnings
            nodes = response_body.get('nodes', [])
            for node in nodes:
                messages = node.get('messages', [])
                for message in messages:
                    if message['kind'] == 'warning':
                        warning_message = message['message']
                        position = message['pos']
                        line = position['line']
                        if any(keyword in warning_message
                               for keyword in warning_keywords):
                            error_details.append(
                                f"Error on line {line}: {message}"
                            )
                            lines.append(line)
                            has_inner_syntax_error = True
        else:
            print("wrong theory name")
            return False, False, [9999], '', '', 9999
        inner_code = ''
        isabelle_lines = isabelle_code.splitlines()
        for line_number in lines:
            index = line_number - 1
            if index < len(isabelle_lines):
                line_text = isabelle_lines[index].strip()

                if "axiomatization where" in line_text:
                    if index + 1 < len(isabelle_lines):
                        inner_code = (inner_code +
                                      isabelle_lines[index + 1].strip() +
                                      '\n'
                                      if inner_code != ''
                                      else
                                      isabelle_lines[index + 1].strip()
                                      + '\n')
                elif "hypothesis" in line_text:
                    if index + 1 < len(isabelle_lines):
                        for i in range(1, 5):
                            if index + i < len(isabelle_lines):
                                inner_code += \
                                    isabelle_lines[index + i].strip() + '\n'
                else:
                    inner_code = inner_code + line_text+'\n'
        error_code_detail = "\n".join(f"{index}. {item}" for index, item in
                                      enumerate(error_details, start=1))

        return has_inner_syntax_error, has_contradiction_error, \
            error_code_detail, inner_code, contradiction_code, \
            solving_time

    # using isabelle client to call isabelle to check
    def critique(self, iteration_number: int,
                 explanation: str,
                 hypothesis: str,
                 premise: Optional[str]):
        theory_name = f'{self.theory_name}_{str(iteration_number)}'
        error_code = ''
        error_comment = ''
        response_body = None
        semantic_validity = True
        solving_time = 0
        tactic_messages = []
        has_syntax_error = False
        proof_sketch = False
        logical_information = ''
        critique_output = {}
        for _ in range(2):
            # first try with sledgehammer directly
            if not proof_sketch:
                (has_syntax_error,
                 logical_information) = self._get_isabelle_syntax_output(
                    theory_name=theory_name,
                    explanation=explanation,
                    hypothesis=hypothesis,
                    premise=premise
                )
            # if has syntax error, return directly
            if has_syntax_error:
                semantic_validity = False
                has_syntax_error = True
                critique_output['semantic validity'] = semantic_validity
                critique_output['syntactic validity'] = False
                critique_output['error code'] = error_code.strip()
                critique_output['solving time'] = solving_time
                critique_output['proof tactics'] = tactic_messages
                critique_output['code'] = self.code
                critique_output['logical information'] = logical_information
                return critique_output
            isabelle_code = self.code
            # use sledgehammer directly
            if not proof_sketch:
                # use sledgehammer
                pattern = r'(proof -).*?(qed)(?!.*qed)'
                sledgehammer_code = re.sub(
                    pattern,
                    r'  sledgehammer\n  oops',
                    isabelle_code,
                    flags=re.DOTALL
                )
                with open(f'formalisation/isabelle/{theory_name}.thy',
                          'w') as f:
                    f.write(sledgehammer_code)
                theories_name = [theory_name]
                # get isabelle output
                (isabelle_response,
                 response_time) = self._get_response(theories_name,
                                                     self.isabelle_dir)
                solving_time += response_time
                finished_response = next(
                    (item for item in isabelle_response
                     if item.response_type == 'FINISHED'),
                    None)
                if finished_response is not None:
                    response_body = json.loads(finished_response.response_body)
                    for node in response_body.get('nodes', []):
                        for message in node.get('messages', []):
                            if 'No proof found' in message.get('message', ''):
                                semantic_validity = False
                                break
                        if not semantic_validity:
                            break
                else:
                    semantic_validity = False

                if semantic_validity:
                    tactic_messages = []
                    for node in response_body.get('nodes', []):
                        for message in node.get('messages', []):
                            tactic_messages.append(message['message'])
                    tactic_to_use = None
                    for item in tactic_messages:
                        if "Try this:" in item:
                            tactic_to_use = item.split("Try this:", 1)[1].strip()
                            last_parenthesis_index = tactic_to_use.rfind('(')
                            if last_parenthesis_index != -1:
                                tactic_to_use = tactic_to_use[:last_parenthesis_index].strip()
                            break
                    if tactic_to_use is None:
                        for item in tactic_messages:
                            if item.strip().startswith("by"):
                                match = re.match(r'by\s*.*?(?=\s*\(\d)',
                                                 item.strip())
                                if match:
                                    tactic_to_use = match.group(0).strip()
                                break
                    if all("no proof found" not in item.lower() for item in tactic_messages):
                        semantic_validity = True
                        if tactic_to_use is not None:
                            lines = sledgehammer_code.split('\n')
                            for i, line in enumerate(lines):
                                if 'sledgehammer' in line and '(*' not in line:
                                    lines[i] = line.replace('sledgehammer',
                                                            tactic_to_use, 1)
                                if 'by by' in line:
                                    lines[i] = line.replace('by by', 'by', 1)
                                if 'oops' in line:
                                    lines[i] = line.replace('oops', '', 1)
                            sledgehammer_code = '\n'.join(lines)

                    with open(f'formalisation/isabelle/{theory_name}.thy',
                              'w') as f:
                        f.write(sledgehammer_code)
                    critique_output['syntactic validity'] = True
                    critique_output['error code'] = ''
                    critique_output['solving time'] = solving_time
                    critique_output['proof tactics'] = tactic_messages
                    critique_output['code'] = self.code
                    critique_output['logical information'] = logical_information
                    critique_output['semantic validity'] = semantic_validity

                    error_keywords = ["Type unification failed",
                                      "Inner lexical error",
                                      "Outer syntax error",
                                      "Inner syntax error",
                                      "Outer lexical error",
                                      "Malformed command syntax",
                                      "Undefined type name"]

                    if any(keyword in message for message in tactic_messages for keyword in error_keywords):
                        semantic_validity = False
                        has_syntax_error = True
                        critique_output['semantic validity'] = semantic_validity
                        critique_output['syntactic validity'] = False
                        critique_output['error code'] = error_code.strip()
                        critique_output['solving time'] = solving_time
                        critique_output['proof tactics'] = tactic_messages
                        critique_output['code'] = self.code
                        critique_output['logical information'] = logical_information
                        return critique_output

                    return critique_output

                if not semantic_validity:
                    with open(f'formalisation/isabelle/{theory_name}.thy', 'w') as f:
                        f.write(isabelle_code)
                    # if the direct sledgehammer failed
                    # go to next loop for using proof sketch to prove
                    proof_sketch = True
                    continue
            else:
                while '<ATP>' in isabelle_code:
                    isa_code_lines = isabelle_code.split('\n')
                    tactic_messages = []
                    for i, line in enumerate(isa_code_lines):
                        if '<ATP>' in line and '(*' not in line:
                            isa_code_lines[i] = line.replace('<ATP>',
                                                             'sledgehammer',
                                                             1)
                            if isa_code_lines[i].count('sledgehammer') > 1:
                                isa_code_lines[i] = \
                                    isa_code_lines[i].replace('sledgehammer',
                                                              '',
                                                              1)
                            error_comment_lines = []
                            for j in range(i-1, -1, -1):
                                if '(*' in isa_code_lines[j]:
                                    error_comment_lines.insert(0, isa_code_lines[j].strip())
                                else:
                                    break
                            error_comment = '\n'.join(error_comment_lines)
                            error_code = (error_comment + '\n' + isa_code_lines[i].strip())
                            break
                    isabelle_code = '\n'.join(isa_code_lines)
                    with open(f'formalisation/isabelle/{theory_name}.thy',
                              'w') as f:
                        f.write(isabelle_code)
                    theories_name = [theory_name]
                    (isabelle_response,
                     response_time) = self._get_response(theories_name,
                                                         self.isabelle_dir)
                    solving_time += response_time
                    finished_response = next(
                        (item for item in isabelle_response
                         if item.response_type == 'FINISHED'),
                        None
                    )
                    if finished_response is not None:
                        response_body = json.loads(finished_response.response_body)
                        for node in response_body.get('nodes', []):
                            for message in node.get('messages', []):
                                tactic_messages.append(message['message'])
                        tactic_to_use = None
                        # print(tactic_messages)
                        for item in tactic_messages:
                            if "Try this:" in item:
                                tactic_to_use = item.split("Try this:", 1)[1].strip()
                                last_parenthesis_index = tactic_to_use.rfind('(')
                                if last_parenthesis_index != -1:
                                    tactic_to_use = tactic_to_use[:last_parenthesis_index].strip()
                                break
                        if tactic_to_use is None:
                            for item in tactic_messages:
                                if item.strip().startswith("by"):
                                    match = re.match(r'by\s*.*?(?=\s*\(\d)',
                                                     item.strip())
                                    if match:
                                        tactic_to_use = match.group(0).strip()
                                    break
                        if all("no proof found" not in item.lower() for item in tactic_messages):
                            semantic_validity = True
                            # if this is the last proof step
                            # we need to check if there is an error
                            if response_body.get('errors') and '<ATP>' not in isabelle_code:
                                semantic_validity = False
                                critique_output['semantic validity'] = semantic_validity
                                critique_output['syntactic validity'] = True
                                critique_output['error code'] = error_code.strip()
                                critique_output['solving time'] = solving_time
                                critique_output['proof tactics'] = []
                                critique_output['code'] = self.code
                                critique_output['logical information'] = logical_information
                                return critique_output
                            if tactic_to_use is not None:
                                lines = isabelle_code.split('\n')
                                for i, line in enumerate(lines):
                                    if 'sledgehammer' in line and '(*' not in line:
                                        lines[i] = line.replace('sledgehammer',
                                                                tactic_to_use, 1)
                                    if 'by by' in line:
                                        lines[i] = line.replace('by by', 'by', 1)
                                isabelle_code = '\n'.join(lines)
                            continue
                        else:
                            semantic_validity = False
                            critique_output['semantic validity'] = semantic_validity
                            critique_output['syntactic validity'] = True
                            critique_output['error code'] = error_code.strip()
                            critique_output['solving time'] = solving_time
                            critique_output['proof tactics'] = []
                            critique_output['code'] = self.code
                            critique_output['logical information'] = logical_information
                            return critique_output
        if semantic_validity:
            critique_output['error code'] = ''
        critique_output['syntactic validity'] = True
        critique_output['solving time'] = solving_time
        critique_output['proof tactics'] = tactic_messages
        critique_output['code'] = self.code
        critique_output['logical information'] = logical_information
        critique_output['semantic validity'] = semantic_validity
        error_keywords = ["Type unification failed", "Inner lexical error",
                          "Outer syntax error", "Inner syntax error",
                          "Outer lexical error", "Malformed command syntax",
                          "Undefined type name"]
        if any(keyword in message for message in tactic_messages for keyword in error_keywords):
            semantic_validity = False
            has_syntax_error = True
            critique_output['semantic validity'] = semantic_validity
            critique_output['syntactic validity'] = False
            critique_output['error code'] = error_code.strip()
            critique_output['solving time'] = solving_time
            critique_output['proof tactics'] = tactic_messages
            critique_output['code'] = self.code
            critique_output['logical information'] = logical_information
            return critique_output

        return critique_output

    def shutdown(self):
        def shutdown_isabelle_sync():
            self.isabelle.shutdown()
            print('Isabelle server shut down')
        # Run the shutdown in a separate thread
        shutdown_thread = threading.Thread(target=shutdown_isabelle_sync)
        shutdown_thread.start()
        shutdown_thread.join()
