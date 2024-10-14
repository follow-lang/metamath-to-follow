
# Metamath to Follow 

Transform metamath database to follow language.

- Github link: `https://github.com/follow-lang/metamath-to-follow` 
- Huggingface link: `https://huggingface.co/datasets/Follow-Lang/set.mm`

## How to use it?

1. Generate the database:

```bash
python -m metamath_to_follow.translator -s ./set.mm/set.mm -o ./follow/set.mm/
```

This command will cost about 3 hours. It will generate two forders:

- `follow/set.mm/code`(425M): the data in follow language format.
- `follow/set.mm/json`(6.3G): the data in json format.

2. Upload to huggingface:

```bash
python -m metamath_to_follow.upload -s ./follow/set.mm -d Follow-Lang/set.mm
```

This command will create "*.zip" file and upload it to huggingface.


## Code Folder Introduction

- `content.follow.json`: stores file list of all follow files.
- `[name].fol`: stores the code of `[name]` block.

## Follow Folder Introduction

- `content.follow.json`: store file list of all json files.
- `[name].json`: stores the imformation of `[name]` block, which can be used for training.
- `types.txt`: stores all name of types.
- `terms.txt`: stores all term content, which can be used to build tokenizer.
- `axioms.txt`: stores all name of axioms.
- `thms.txt`: stores all name of thms.

### Block `type` 

```json
{
    "type": "type",
    "label": <LABEL>
}
```

### Block `term` 

```json
{
    "type": "term",
    "label": <LABEL>,
    "type": <TYPE>,
    "args": ["<TYPE> <NAME>", "<TYPE> <NAME>", ...],
    "stmt": <STMT SEQUENCE>
}
```

### Block `axiom` 

```json
{
    "type": "axiom",
    "label": <LABEL>,
    "args": ["<TYPE> <NAME>", "<TYPE> <NAME>", ...],
    "target": [<STMT SEQUENCE>],
    "conditions": [<STMT SEQUENCE>, <STMT SEQUENCE>, ...],
    "dvs": [(<V1>, <V2>), (<V3>, <V4>), ...],
}
```

### Block `thm`

```json
{
    "type": "thm",
    "label": <LABEL>,
    "args": ["<TYPE> <NAME>", "<TYPE> <NAME>", ...],
    "target": [<STMT SEQUENCE>],
    "conditions": [<STMT SEQUENCE>, <STMT SEQUENCE>, ...],
    "dvs": [(<V>, <V>), (<V>, <V>), ...],
    "states": [<STATE>, <STATE>, ...],
    "actions": [ <ACTION>, <ACTION>, ...],
    "operators": [ <OP>, <OP>, ...]
}
```

- `<STATE>` is combined with target statements and diff statements.
- `<ACTION>` is combined with target statements, assumptions and diff statements.
- `<OP>` is a function call of axiom or theorem.
