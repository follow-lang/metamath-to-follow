import argparse
import os
import time  # 用于控制请求频率
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


def upload_with_progress(
    api, file_path, repo_id, path_in_repo, chunk_size=50 * 1024 * 1024
):
    """将文件分块上传，避免请求过于频繁。"""
    total_size = os.path.getsize(file_path)  # 获取文件大小
    with open(file_path, "rb") as f:  # 以二进制模式打开文件
        with tqdm(total=total_size, unit="B", unit_scale=True, desc="上传中") as pbar:
            while True:
                chunk = f.read(chunk_size)  # 每次读取 chunk_size 大小的块
                if not chunk:
                    break
                # 进行上传
                try:
                    api.upload_file(
                        path_or_fileobj=f,  # 传递文件对象
                        path_in_repo=path_in_repo,
                        repo_id=repo_id,
                        repo_type="dataset",
                    )
                    pbar.update(len(chunk))  # 更新进度条

                    # 控制请求频率，防止 API 限制
                    time.sleep(1)  # 每次上传后暂停1秒（可以根据需要调整）
                except Exception as e:
                    print(f"上传失败: {e}")
                    break


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

    # 通过 upload_with_progress 进行分块上传
    try:
        upload_with_progress(api, output_zip, repo_id, path_in_repo)
    except Exception as e:
        print("Upload failed", e)
