Blockly.JavaScript['observation_andobs'] = function(block) {
  var value_observation1 = Blockly.JavaScript.valueToCode(block, 'observation1', Blockly.JavaScript.ORDER_ATOMIC);
  var value_observation2 = Blockly.JavaScript.valueToCode(block, 'observation2', Blockly.JavaScript.ORDER_ATOMIC);
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['observation_belowtimeout'] = function(block) {
  var text_block_number = block.getFieldValue('block_number');
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['observation_falseobs'] = function(block) {
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['observation_notobs'] = function(block) {
  var value_observation = Blockly.JavaScript.valueToCode(block, 'observation', Blockly.JavaScript.ORDER_ATOMIC);
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['observation_orobs'] = function(block) {
  var value_observation1 = Blockly.JavaScript.valueToCode(block, 'observation1', Blockly.JavaScript.ORDER_ATOMIC);
  var value_observation2 = Blockly.JavaScript.valueToCode(block, 'observation2', Blockly.JavaScript.ORDER_ATOMIC);
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['observation_personchosesomething'] = function(block) {
  var text_choice_id = block.getFieldValue('choice_id');
  var text_person = block.getFieldValue('person');
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['observation_personchosethis'] = function(block) {
  var text_choice_id = block.getFieldValue('choice_id');
  var text_person = block.getFieldValue('person');
  var text_choice_value = block.getFieldValue('choice_value');
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['observation_timeabove'] = function(block) {
  var text_block_number = block.getFieldValue('block_number');
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['observation_trueobs'] = function(block) {
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['base_contract'] = function(block) {
  var statements_base_contract = Blockly.JavaScript.statementToCode(block, 'base_contract');
  // TODO: Assemble JavaScript into code variable.
  var code = '...;\n';
  return code;
};

Blockly.JavaScript['contract_null'] = function(block) {
  // TODO: Assemble JavaScript into code variable.
  var code = '...;\n';
  return code;
};

Blockly.JavaScript['contract_redeemcc'] = function(block) {
  var number_ccommit_id = block.getFieldValue('ccommit_id');
  var statements_contract = Blockly.JavaScript.statementToCode(block, 'contract');
  // TODO: Assemble JavaScript into code variable.
  var code = '...;\n';
  return code;
};

Blockly.JavaScript['contract_pay'] = function(block) {
  var number_pay_id = block.getFieldValue('pay_id');
  var number_payer_id = block.getFieldValue('payer_id');
  var number_ammount = block.getFieldValue('ammount');
  var number_payee_id = block.getFieldValue('payee_id');
  var number_expiration = block.getFieldValue('expiration');
  var statements_contract = Blockly.JavaScript.statementToCode(block, 'contract');
  // TODO: Assemble JavaScript into code variable.
  var code = '...;\n';
  return code;
};

Blockly.JavaScript['contract_both'] = function(block) {
  var statements_contract1 = Blockly.JavaScript.statementToCode(block, 'contract1');
  var statements_contract2 = Blockly.JavaScript.statementToCode(block, 'contract2');
  // TODO: Assemble JavaScript into code variable.
  var code = '...;\n';
  return code;
};

Blockly.JavaScript['contract_choice'] = function(block) {
  var value_observation = Blockly.JavaScript.valueToCode(block, 'observation', Blockly.JavaScript.ORDER_ATOMIC);
  var statements_contract1 = Blockly.JavaScript.statementToCode(block, 'contract1');
  var statements_contract2 = Blockly.JavaScript.statementToCode(block, 'contract2');
  // TODO: Assemble JavaScript into code variable.
  var code = '...;\n';
  return code;
};

Blockly.JavaScript['contract_commitcash'] = function(block) {
  var number_ccommit_id = block.getFieldValue('ccommit_id');
  var number_person_id = block.getFieldValue('person_id');
  var number_ammount = block.getFieldValue('ammount');
  var number_end_expiration = block.getFieldValue('end_expiration');
  var number_start_expiration = block.getFieldValue('start_expiration');
  var statements_contract1 = Blockly.JavaScript.statementToCode(block, 'contract1');
  var statements_contract2 = Blockly.JavaScript.statementToCode(block, 'contract2');
  // TODO: Assemble JavaScript into code variable.
  var code = '...;\n';
  return code;
};

Blockly.JavaScript['contract_when'] = function(block) {
  var value_observation = Blockly.JavaScript.valueToCode(block, 'observation', Blockly.JavaScript.ORDER_ATOMIC);
  var statements_contract1 = Blockly.JavaScript.statementToCode(block, 'contract1');
  var number_timeout = block.getFieldValue('timeout');
  var statements_contract2 = Blockly.JavaScript.statementToCode(block, 'contract2');
  // TODO: Assemble JavaScript into code variable.
  var code = '...;\n';
  return code;
};

Blockly.JavaScript['observation_value_ge'] = function(block) {
  var value_value1 = Blockly.JavaScript.valueToCode(block, 'value1', Blockly.JavaScript.ORDER_ATOMIC);
  var value_value2 = Blockly.JavaScript.valueToCode(block, 'value2', Blockly.JavaScript.ORDER_ATOMIC);
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['value_available_money'] = function(block) {
  var number_commit_id = block.getFieldValue('commit_id');
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['value_add_money'] = function(block) {
  var value_value1 = Blockly.JavaScript.valueToCode(block, 'value1', Blockly.JavaScript.ORDER_ATOMIC);
  var value_value2 = Blockly.JavaScript.valueToCode(block, 'value2', Blockly.JavaScript.ORDER_ATOMIC);
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};

Blockly.JavaScript['value_const_money'] = function(block) {
  var number_money = block.getFieldValue('money');
  // TODO: Assemble JavaScript into code variable.
  var code = '...';
  // TODO: Change ORDER_NONE to the correct strength.
  return [code, Blockly.JavaScript.ORDER_NONE];
};