import argparse
import os
import zipfile

from huggingface_hub import HfApi
from tqdm import tqdm


def zip_dataset(dataset_dir, output_zip):
    file_list = []  # 创建文件列表
    for root, dirs, files in os.walk(dataset_dir):
        for file in files:
            file_path = os.path.join(root, file)
            file_list.append(file_path)  # 收集文件路径

    with zipfile.ZipFile(output_zip, "w", zipfile.ZIP_DEFLATED) as zipf:
        for file_path in tqdm(file_list, desc="压缩中", unit="文件"):  # 添加进度条
            zipf.write(file_path, os.path.relpath(file_path, dataset_dir))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Upload dataset")
    parser.add_argument(
        "-s",
        "--source-folder",
        dest="source_folder",
        type=str,
        help="Database source folder",
    )
    parser.add_argument(
        "-d",
        "--repo-id",
        dest="repo_id",
        type=str,
        help="Hugging Face repo ID",
    )
    args = parser.parse_args()

    dataset_dir = args.source_folder
    folder_name = os.path.basename(dataset_dir)
    output_zip = dataset_dir + ".zip"

    # 先压缩数据集
    zip_dataset(dataset_dir, output_zip)

    # 上传数据集到 Hugging Face
    api = HfApi()
    repo_id = args.repo_id
    path_in_repo = f"datasets/{folder_name}.zip"

    # 通过 upload_with_progress 进行直接上传
    with open(output_zip, "rb") as f:  # 以二进制模式打开文件
        # 进行上传
        try:
            print("开始上传到Hugging Face")
            api.upload_file(
                path_or_fileobj=f,  # 传递文件对象
                path_in_repo=path_in_repo,
                repo_id=repo_id,
                repo_type="dataset",
            )
            print("上传成功")  # 上传成功提示
        except Exception as e:
            print(f"上传失败: {e}")
