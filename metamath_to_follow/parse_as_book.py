import io
from enum import Enum


class HeadSymbol(Enum):
    PART = "###############################################################################"
    H1 = "#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#"
    H2 = "=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-="
    H3 = "-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-"


class HeadState(Enum):
    TEXT = -1
    PART = 0
    H1 = 1
    H2 = 2
    H3 = 3


def scan(file: io.TextIOWrapper):
    in_comment_block = False
    comments = []
    label = None

    state = HeadState.TEXT

    line = file.readline()

    while line:
        line = line.strip()
        if line in [symbol.value for symbol in HeadSymbol]:
            state = (
                HeadState.PART
                if line == HeadSymbol.PART.value and state != HeadState.PART
                else HeadState.H1
                if line == HeadSymbol.H1.value and state != HeadState.H1
                else HeadState.H2
                if line == HeadSymbol.H2.value and state != HeadState.H2
                else HeadState.H3
                if line == HeadSymbol.H3.value and state != HeadState.H3
                else HeadState.TEXT
            )
        elif state in [HeadState.PART, HeadState.H1, HeadState.H2, HeadState.H3]:
            if len(comments) > 0:
                yield ("comment", " ".join(comments))
                comments = []
            yield (state.name.lower(), line)  # 使用状态名称作为类型
        else:
            tokens = line.split()
            for token in tokens:
                if in_comment_block:
                    if token == "$)":
                        yield ("comment", " ".join(comments))
                        in_comment_block = False
                        comments = []
                    else:
                        comments.append(token)
                elif token == "$(":
                    in_comment_block = True
                elif token in ["$c", "$v", "$d", "$f", "$a", "$p"]:
                    if label is not None and label[0] != "$":
                        yield ("label", label)
                else:
                    label = token
        line = file.readline()


if __name__ == "__main__":
    import argparse
    import os

    parser = argparse.ArgumentParser(
        description="""Get comments from setmm 
    Example:
        '$ python3 parse_as_book.py <source_file> <output_folder>'
    """
    )
    parser.add_argument(
        "-s",
        "--source-file",
        dest="source_file",
        type=str,
        help="""metamath source file""",
    )
    parser.add_argument(
        "-o",
        "--output-folder",
        dest="output_folder",
        type=str,
        default="output",
        help="""output folder""",
    )
    args = parser.parse_args()
    source_file = args.source_file  # 修改这一行
    output_folder = args.output_folder

    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    book_f = open(os.path.join(output_folder, "book-content.txt"), "w")

    with open(source_file, "r") as f:
        for block in scan(f):
            book_f.write(f"{block[0]}\t{block[1]}\n")
    book_f.close()
