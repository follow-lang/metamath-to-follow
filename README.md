
# Pure Training Data

- The data is located in datasets/train.
- Each line is formatted as: Cost(s) Cost(a) Cost(s')\t s a s' .
- Cost(s) = max(Cost(a), 1+Cost(s')).
- The maximum word length is 2048.
- All vocabulary words are listed in datasets/words.txt.
- The data was generated with a depth of 2.

If you need additional data, feel free to reach out.

This version improves readability and flow while maintaining the original meaning.

# Metamath to Follow 

Transform metamath database to follow language.

- Github link: `https://github.com/follow-lang/metamath-to-follow` 
- Huggingface link: `https://huggingface.co/datasets/Follow-Lang/set.mm`

## How to use it?

1. Generate the database:

```bash
python -m metamath_to_follow.translator -s ./set.mm/set.mm -o ./follow/set.mm/
```

This command will cost about 3 hours. It will generate these:

- `follow/set.mm/code`(329M): the data in follow language format.
- `follow/set.mm/json`(9.6G): the data in json format.
- `follow/set.mm/words.txt`: words used in train folder. It includes some special token.
- `follow/set.mm/types.txt`: stores all name of types.
- `follow/set.mm/terms.txt`: stores all term content, which can be used to build tokenizer.
- `follow/set.mm/axioms.txt`: stores all name of axioms.
- `follow/set.mm/thms.txt`: stores all name of thms.

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
    "args": [[<TYPE>, <NAME>], [<TYPE>, <NAME>], ...],
    "targets": [<STMT SEQUENCE>],
    "conditions": [<STMT SEQUENCE>, <STMT SEQUENCE>, ...],
    "dvs": [(<V1>, <V2>), (<V3>, <V4>), ...],
    "cost": 1
}
```

### Block `thm`

```json
{
    "type": "thm",
    "label": <LABEL>,
    "args": [[<TYPE>, <NAME>], [<TYPE>, <NAME>], ...],
    "targets": [<STMT SEQUENCE>],
    "conditions": [<STMT SEQUENCE>, <STMT SEQUENCE>, ...],
    "dvs": [(<V>, <V>), (<V>, <V>), ...],
    "states": [<STATE>, <STATE>, ...],
    "actions": [ <ACTION>, <ACTION>, ...],
    "operators": [ <OP>, <OP>, ...],
    "cost": <COST>,
    "state_costs": [<COST>, <COST>, ...],
    "action_costs": [<COST>, <COST>, ...],
}
```

- `<STATE>` is combined with target statements.
- `<ACTION>` is combined with target statements, assumptions and diff statements.
- `<OP>` is a function call of axiom or theorem, `<OP> = [<LABEL>, [<ARG>, <ARG>, ...]]`.
- `<COST>` is the max number of proof ops: `Cost(s) = max(Cost(a), Cost(s')+1)`.