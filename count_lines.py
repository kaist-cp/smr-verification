#!/usr/bin/env python3
import subprocess
import re


def str_ratio(idx, res):
    return " (" + str(round((res[idx] / res[0] - 1) * 100, 1)) + "%)"


def count_coqwc_lines(ds_file):
    """Runs the coqwc command on a file and parses the number of spec and proof lines.
    Write the tuple (file_name, spec_lines + proof_lines) to line_count.csv in csv format
    ."""

    prefix = "./theories/"
    res_code = []
    res_proof = []

    for recl in ["no_recl", "hazptr", "ebr"]:
        if ds_file["name"] == "Harris Set" and recl == "hazptr":
            res_code += [0]
            res_proof += [0]
            continue

        code_count = 0
        for code in ds_file["code"]:
            lines = subprocess.check_output(
                ["coqwc", prefix + recl + "/" + code + ".v"]
            ).decode("utf-8")
            match = re.findall(r"(\d+)", lines)
            code_count += int(match[0])

        proof_count = 0
        for proof in ds_file["proofs"]:
            lines = subprocess.check_output(
                ["coqwc", prefix + recl + "/" + proof + ".v"]
            ).decode("utf-8")
            match = re.findall(r"(\d+)", lines)
            proof_count += int(match[0]) + int(match[1])
        res_code += [code_count]
        res_proof += [proof_count]

    return (res_code, res_proof)


clq_files = {
    "name": "Chase-Lev Deque",
    "code": ["code_cldeque"],
    "proofs": ["spec_cldeque", "proof_cldeque"],
}
counter_files = {
    "name": "Counter",
    "code": ["code_counter"],
    "proofs": ["spec_counter", "proof_counter"],
}
dglm_files = {
    "name": "DGLM Queue",
    "code": ["code_dglm"],
    "proofs": ["spec_queue", "proof_dglm"],
}
estack_files = {
    "name": "Elimination Stack",
    "code": ["code_elimstack"],
    "proofs": ["spec_stack", "proof_elimstack"],
}
harris_files = {
    "name": "Harris Set",
    "code": ["code_harris_operations", "code_harris_find"],
    "proofs": ["spec_ordered_set", "proof_harris_operations", "proof_harris_find"],
}
hm_files = {
    "name": "Harris-Michael Set",
    "code": ["code_harris_operations", "code_harris_michael_find"],
    "proofs": [
        "spec_ordered_set",
        "proof_harris_operations",
        "proof_harris_michael_find",
    ],
}
ms_files = {
    "name": "Michael-Scott Queue",
    "code": ["code_ms"],
    "proofs": ["spec_queue", "proof_ms"],
}
rdcss_files = {
    "name": "RDCSS",
    "code": ["code_rdcss"],
    "proofs": ["spec_rdcss", "proof_rdcss"],
}
tstack_files = {
    "name": "Treiber Stack",
    "code": ["code_treiber"],
    "proofs": ["spec_stack", "proof_treiber"],
}

ds_files = [
    counter_files,
    tstack_files,
    estack_files,
    ms_files,
    dglm_files,
    harris_files,
    hm_files,
    clq_files,
    rdcss_files,
]

if __name__ == "__main__":
    with open("line_count.tsv", "w") as f:
        f.write(
            "Data Structure\tNR Code\tHP Code\tRCU Code\tNR Proof\tHP Proof\tRCU Proof\n"
        )
    format_com = lambda i: f"{i:,}"
    total_code = [0, 0, 0]
    total_proof = [0, 0, 0]
    all_ds_res = []
    for ds_file in ds_files:
        (res_code, res_proof) = count_coqwc_lines(ds_file)
        total_code = [sum(i) for i in zip(total_code, res_code)]
        total_proof = [sum(i) for i in zip(total_proof, res_proof)]

        res_code_str = list(map(format_com, res_code))
        res_proof_str = list(map(format_com, res_proof))

        res_code_str[1] += str_ratio(1, res_code)
        res_code_str[2] += str_ratio(2, res_code)

        res_proof_str[1] += str_ratio(1, res_proof)
        res_proof_str[2] += str_ratio(2, res_proof)
        res = res_code_str + res_proof_str
        with open("line_count.tsv", "a") as f:
            f.write(ds_file["name"] + "\t" + "\t".join(res) + "\n")

    (harris_code, harris_proof) = count_coqwc_lines(harris_files)
    total_code_str = list(map(format_com, total_code))
    total_proof_str = list(map(format_com, total_proof))

    total_code_str[2] += str_ratio(2, total_code)
    total_proof_str[2] += str_ratio(2, total_proof)

    total_code[0] -= harris_code[0]
    total_proof[0] -= harris_proof[0]

    total_code_str[0] = f"{total_code[0]:,}" + " " + total_code_str[0]
    total_proof_str[0] = f"{total_proof[0]:,}" + " " + total_proof_str[0]

    total_code_str[1] += str_ratio(1, total_code)
    total_proof_str[1] += str_ratio(1, total_proof)

    total = total_code_str + total_proof_str
    with open("line_count.tsv", "a") as f:
        f.write("total" + "\t" + "\t".join(total) + "\n")
