def train_nanogpt_on_file(
    file_name: str,
    dataset_name: str | None = None,
    out_dir: str | None = None,
    train_split: float = 0.9,
    max_iters: int = 20000,
    eval_interval: int = 1000,
    log_interval: int = 1,
    batch_size: int = 12,
    block_size: int = 1024,
    n_layer: int = 6,
    n_head: int = 6,
    n_embd: int = 384,
    num_params = 2478690,
    learning_rate: float = 2e-2,
    compile_model: bool = False,
    device: str | None = None,
):
    project_root = Path(globals().get('PROJECT_ROOT', Path.cwd()))
    pkg_root = Path(globals().get('PKG_ROOT', project_root / 'nanoGPT-20251228T135841Z-3-001' / 'nanoGPT'))
    def estimate_num_params(n_layer: int, n_head: int, n_embd: int, vocab_size: int, block_size: int) -> int:
        return (
            vocab_size * n_embd
            + block_size * n_embd
            + n_layer * (12 * n_embd * n_embd + 2 * n_embd)
            + 2 * n_embd
        )
    def choose_model_size_for_target(target: int, vocab_size: int, block_size: int) -> tuple[int, int, int, int]:
        best = None
        for embd in range(128, 2049, 64):
            for layers in range(2, 49):
                for heads in range(2, 33):
                    if embd % heads != 0:
                        continue
                    params = estimate_num_params(layers, heads, embd, vocab_size, block_size)
                    cand = (abs(params - target), params, layers, heads, embd)
                    if best is None or cand < best:
                        best = cand
        if best is None:
            raise ValueError("Nie udało się dobrać konfiguracji modelu dla num_params.")
        _, params, layers, heads, embd = best
        return layers, heads, embd, params
    if not (pkg_root / 'train.py').exists():
        alt_pkg_root = project_root / 'nanoGPT'
        if (alt_pkg_root / 'train.py').exists():
            pkg_root = alt_pkg_root
        else:
            raise FileNotFoundError(f'Nie znaleziono train.py w {pkg_root} ani {alt_pkg_root}.')
    src = Path(file_name).expanduser()
    if not src.is_absolute():
        from_project = (project_root / src).resolve()
        from_cwd = (Path.cwd() / src).resolve()
        src = from_project if from_project.exists() else from_cwd
    if not src.exists():
        raise FileNotFoundError(f'Nie znaleziono pliku wejsciowego: {src}')
    if dataset_name is None:
        dataset_name = re.sub(r'[^0-9A-Za-z_]+', '_', src.stem).strip('_') or 'custom_char'
    data_dir = pkg_root / 'data' / dataset_name
    data_dir.mkdir(parents=True, exist_ok=True)
    input_txt = data_dir / 'input.txt'
    shutil.copy2(src, input_txt)
    text = input_txt.read_text(encoding='utf-8')
    if len(text) < 2:
        raise ValueError('Plik wejsciowy jest zbyt krotki do podzialu train/val.')
    chars = sorted(set(text))
    vocab_size = len(chars)
    if vocab_size > 65535:
        raise ValueError('Za duzo unikalnych znakow dla kodowania uint16.')
    stoi = {ch: i for i, ch in enumerate(chars)}
    itos = {i: ch for i, ch in enumerate(chars)}
    ids = np.array([stoi[ch] for ch in text], dtype=np.uint16)
    print(ids.__len__())
    split_idx = int(len(ids) * train_split)
    split_idx = max(1, min(len(ids) - 1, split_idx))
    train_ids = ids[:split_idx]
    val_ids = ids[split_idx:]
    train_ids.tofile(data_dir / 'train.bin')
    val_ids.tofile(data_dir / 'val.bin')
    meta = {'vocab_size': vocab_size, 'itos': itos, 'stoi': stoi}
    with open(data_dir / 'meta.pkl', 'wb') as f:
        pickle.dump(meta, f)
    print(ids.__len__()/20)
    if num_params is not None:
        n_layer, n_head, n_embd, estimated_params = choose_model_size_for_target(
            num_params, vocab_size, block_size
        )
        print(f'Wybrana konfiguracja pod num_params={num_params}:')
        print(f'  n_layer={n_layer}, n_head={n_head}, n_embd={n_embd}')
        print(f'  szacowana liczba parametrów: {estimated_params}')
    else:
        estimated_params = estimate_num_params(n_layer, n_head, n_embd, vocab_size, block_size)
        print(f'Szacowana liczba parametrów: {estimated_params}')
# ... existing code ...
    if out_dir is None:
        model_out_dir = pkg_root / f'out-{dataset_name}'
    else:
        model_out_dir = Path(out_dir)
        if not model_out_dir.is_absolute():
            model_out_dir = pkg_root / model_out_dir
    if device is None:
        device = 'cuda' if shutil.which('nvidia-smi') else 'cpu'
    print(f'Plik wejsciowy: {src.resolve()}')
    print(f'Model bedzie zapisany w: {model_out_dir.resolve()}')
    print(f'Dataset nanoGPT: {dataset_name}')
    cmd = [
        sys.executable,
        'train.py',
        f'--dataset={dataset_name}',
        f'--out_dir={model_out_dir}',
        f'--max_iters={max_iters}',
        f'--eval_interval={eval_interval}',
        f'--log_interval={log_interval}',
        f'--batch_size={batch_size}',
        f'--block_size={block_size}',
        f'--n_layer={n_layer}',
        f'--n_head={n_head}',
        f'--n_embd={n_embd}',
        f'--learning_rate={learning_rate}',
        f'--device={device}',
        f'--compile={compile_model}',
        '--always_save_checkpoint=True'
    ]
    process = subprocess.Popen(
        cmd,
        cwd=str(pkg_root),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    if process.stdout is None:
        raise RuntimeError('Nie udalo sie przechwycic logow treningu.')
    for line in process.stdout:
        print(line, end='')
    return_code = process.wait()
    if return_code != 0:
        raise RuntimeError(f'Trening nanoGPT zakonczyl sie kodem {return_code}.')
    return model_out_dir


def finetune_nanogpt_on_file(
    file_name: str,
    base_model: str,
    dataset_name: str | None = None,
    out_dir: str | None = None,
    train_split: float = 0.9,
    max_iters: int = 20000,
    eval_interval: int = 1000,
    log_interval: int = 1,
    batch_size: int = 12,
    block_size: int = 1024,
    learning_rate: float = 1e-3,
    compile_model: bool = False,
    device: str | None = None,
):
    project_root = Path(globals().get('PROJECT_ROOT', Path.cwd()))
    pkg_root = Path(globals().get('PKG_ROOT', project_root / 'nanoGPT-20251228T135841Z-3-001' / 'nanoGPT'))

    if not (pkg_root / 'train.py').exists():
        alt_pkg_root = project_root / 'nanoGPT'
        if (alt_pkg_root / 'train.py').exists():
            pkg_root = alt_pkg_root
        else:
            raise FileNotFoundError(f'Nie znaleziono train.py w {pkg_root} ani {alt_pkg_root}.')

    src = Path(file_name).expanduser()
    if not src.is_absolute():
        from_project = (project_root / src).resolve()
        from_cwd = (Path.cwd() / src).resolve()
        src = from_project if from_project.exists() else from_cwd
    if not src.exists():
        raise FileNotFoundError(f'Nie znaleziono pliku wejsciowego: {src}')

    base_model_path = Path(base_model).expanduser()
    if not base_model_path.is_absolute():
        from_project = (project_root / base_model_path).resolve()
        from_cwd = (Path.cwd() / base_model_path).resolve()
        from_pkg = (pkg_root / base_model_path).resolve()
        if from_project.exists():
            base_model_path = from_project
        elif from_cwd.exists():
            base_model_path = from_cwd
        else:
            base_model_path = from_pkg

    ckpt_src = base_model_path / 'ckpt.pt' if base_model_path.is_dir() else base_model_path
    if ckpt_src.name != 'ckpt.pt':
        raise ValueError('Argument base_model musi wskazywac katalog modelu albo plik ckpt.pt.')
    if not ckpt_src.exists():
        raise FileNotFoundError(f'Nie znaleziono checkpointu: {ckpt_src}')
    source_out_dir = ckpt_src.parent

    import torch

    checkpoint = torch.load(ckpt_src, map_location='cpu')
    checkpoint_cfg = checkpoint.get('config', {})
    checkpoint_model_args = checkpoint.get('model_args', {})
    checkpoint_dataset = checkpoint_cfg.get('dataset')
    checkpoint_block_size = checkpoint_model_args.get('block_size')
    checkpoint_vocab_size = checkpoint_model_args.get('vocab_size')

    if checkpoint_dataset is None:
        raise ValueError('Checkpoint nie zawiera nazwy datasetu w config[\'dataset\'].')

    source_meta_path = pkg_root / 'data' / checkpoint_dataset / 'meta.pkl'
    if not source_meta_path.exists():
        raise FileNotFoundError(f'Nie znaleziono tokenizera modelu: {source_meta_path}')

    with open(source_meta_path, 'rb') as f:
        source_meta = pickle.load(f)

    stoi = source_meta.get('stoi')
    itos = source_meta.get('itos')
    vocab_size = source_meta.get('vocab_size')
    if not isinstance(stoi, dict) or not isinstance(itos, dict):
        raise ValueError('Niepoprawny format source meta.pkl (brak stoi/itos).')

    if checkpoint_vocab_size is not None and vocab_size != checkpoint_vocab_size:
        raise ValueError(
            'Niezgodny vocab_size miedzy checkpointem a tokenizerem: '
            f'{checkpoint_vocab_size} != {vocab_size}'
        )

    text = src.read_text(encoding='utf-8')
    if len(text) < 2:
        raise ValueError('Plik wejsciowy jest zbyt krotki do podzialu train/val.')

    unknown_chars = sorted({ch for ch in text if ch not in stoi})
    if unknown_chars:
        preview = ''.join(unknown_chars[:20])
        raise ValueError(
            f'Tekst zawiera {len(unknown_chars)} znakow spoza tokenizera modelu. '
            f'Przyklad: {preview!r}'
        )

    ids = np.array([stoi[ch] for ch in text], dtype=np.uint16)
    split_idx = int(len(ids) * train_split)
    split_idx = max(1, min(len(ids) - 1, split_idx))
    train_ids = ids[:split_idx]
    val_ids = ids[split_idx:]

    if dataset_name is None:
        base_dataset = re.sub(r'[^0-9A-Za-z_]+', '_', src.stem).strip('_') or 'custom_char'
        dataset_name = f'{base_dataset}_finetune'

    data_dir = pkg_root / 'data' / dataset_name
    data_dir.mkdir(parents=True, exist_ok=True)
    input_txt = data_dir / 'input.txt'
    shutil.copy2(src, input_txt)
    train_ids.tofile(data_dir / 'train.bin')
    val_ids.tofile(data_dir / 'val.bin')

    meta = {
        'vocab_size': vocab_size,
        'itos': itos,
        'stoi': stoi,
    }
    with open(data_dir / 'meta.pkl', 'wb') as f:
        pickle.dump(meta, f)

    if out_dir is None:
        model_out_dir = source_out_dir
    else:
        model_out_dir = Path(out_dir)
        if not model_out_dir.is_absolute():
            model_out_dir = pkg_root / model_out_dir
    model_out_dir.mkdir(parents=True, exist_ok=True)

    ckpt_dst = model_out_dir / 'ckpt.pt'
    if ckpt_dst.resolve() != ckpt_src.resolve():
        shutil.copy2(ckpt_src, ckpt_dst)

    if block_size is None:
        block_size = checkpoint_block_size
    if block_size is None:
        raise ValueError('Nie mozna ustalic block_size z checkpointu. Podaj block_size recznie.')
    if checkpoint_block_size is not None and block_size > checkpoint_block_size:
        raise ValueError(
            f'block_size={block_size} nie moze byc wiekszy niz block_size modelu ({checkpoint_block_size}).'
        )

    if device is None:
        device = 'cuda' if shutil.which('nvidia-smi') else 'cpu'

    print(f'Plik wejsciowy: {src.resolve()}')
    print(f'Checkpoint bazowy: {ckpt_src.resolve()}')
    print(f'Model bedzie zapisany w: {model_out_dir.resolve()}')
    print(f'Dataset nanoGPT: {dataset_name}')

    cmd = [
        sys.executable,
        'train.py',
        f'--dataset={dataset_name}',
        f'--out_dir={model_out_dir}',
        '--init_from=resume',
        f'--max_iters={max_iters}',
        f'--eval_interval={eval_interval}',
        f'--log_interval={log_interval}',
        f'--batch_size={batch_size}',
        f'--block_size={block_size}',
        f'--learning_rate={learning_rate}',
        f'--device={device}',
        f'--compile={compile_model}',
        '--always_save_checkpoint=True',
    ]

    process = subprocess.Popen(
        cmd,
        cwd=str(pkg_root),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )

    if process.stdout is None:
        raise RuntimeError('Nie udalo sie przechwycic logow treningu.')

    for line in process.stdout:
        print(line, end='')

    return_code = process.wait()
    if return_code != 0:
        raise RuntimeError(f'Dotrenowanie nanoGPT zakonczyl sie kodem {return_code}.')

    return model_out_dir


class NanoGPTBundle:
    model: GPT
    encode: Callable[[str], list[int]]
    device: str
    device_type: str
    ptdtype: torch.dtype
@dataclass
class NanoGPTBundle:
    model: GPT
    encode: Callable[[str], list[int]]
    decode_token: Callable[[int], str]         # <-- NOWE: id -> tekst tokenu
    decode_ids: Callable[[list[int]], str]     # <-- NOWE: lista id -> tekst
    device: str
    device_type: str
    ptdtype: torch.dtype

def load_nanogpt_bundle(
    out_dir: str,
    *,
    device: Optional[str] = None,
    dtype: Optional[str] = None,
) -> NanoGPTBundle:
    if device is None:
        device = "cuda" if torch.cuda.is_available() else "cpu"
    requested_device = device
    requested_device_type = "cuda" if "cuda" in requested_device else "cpu"
    if dtype is None:
        if requested_device_type == "cuda" and torch.cuda.is_bf16_supported():
            dtype = "bfloat16"
        elif requested_device_type == "cuda":
            dtype = "float16"
        else:
            dtype = "float32"
    ptdtype = {"float32": torch.float32, "float16": torch.float16, "bfloat16": torch.bfloat16}[dtype]
    project_root = os.path.abspath(globals().get("PROJECT_ROOT", os.getcwd()))
    raw_pkg_roots = [
        globals().get("PKG_ROOT"),
        os.path.join(project_root, "nanoGPT-20251228T135841Z-3-001", "nanoGPT"),
        os.path.join(project_root, "nanoGPT"),
    ]
    pkg_roots = []
    for root in raw_pkg_roots:
        if not root:
            continue
        root_abs = os.path.abspath(os.path.expanduser(str(root)))
        if root_abs in pkg_roots:
            continue
        if os.path.exists(os.path.join(root_abs, "train.py")):
            pkg_roots.append(root_abs)
    if not pkg_roots:
        raise FileNotFoundError("Nie znaleziono katalogu nanoGPT z train.py.")
    out_dir_path = os.path.expanduser(out_dir)
    ckpt_candidates = []
    if os.path.isabs(out_dir_path):
        ckpt_candidates.append(out_dir_path if out_dir_path.endswith("ckpt.pt") else os.path.join(out_dir_path, "ckpt.pt"))
    else:
        for root in pkg_roots:
            base = os.path.join(root, out_dir_path)
            ckpt_candidates.append(base if out_dir_path.endswith("ckpt.pt") else os.path.join(base, "ckpt.pt"))
        project_base = os.path.join(project_root, out_dir_path)
        ckpt_candidates.append(project_base if out_dir_path.endswith("ckpt.pt") else os.path.join(project_base, "ckpt.pt"))
    ckpt_path = next((p for p in ckpt_candidates if os.path.exists(p)), None)
    if ckpt_path is None:
        raise FileNotFoundError(
            "Nie znaleziono checkpointu. Sprawdzane sciezki: " + "; ".join(ckpt_candidates)
        )
    real_ckpt_path = os.path.realpath(ckpt_path)
    ckpt_pkg_root = next(
        (root for root in pkg_roots if os.path.commonpath([real_ckpt_path, os.path.realpath(root)]) == os.path.realpath(root)),
        None,
    )
    if ckpt_pkg_root is None:
        inferred_root = os.path.dirname(os.path.dirname(real_ckpt_path))
        if os.path.exists(os.path.join(inferred_root, "train.py")):
            ckpt_pkg_root = inferred_root
        else:
            ckpt_pkg_root = pkg_roots[0]
    checkpoint = torch.load(real_ckpt_path, map_location="cpu", weights_only=False)
    gptconf = GPTConfig(**checkpoint["model_args"])
    model = GPT(gptconf)
    state_dict = checkpoint["model"]
    unwanted_prefix = "_orig_mod."
    for k in list(state_dict.keys()):
        if k.startswith(unwanted_prefix):
            state_dict[k[len(unwanted_prefix):]] = state_dict.pop(k)
    model.load_state_dict(state_dict)
    active_device = requested_device
    active_device_type = requested_device_type
    active_ptdtype = ptdtype
    try:
        model.eval().to(active_device)
    except Exception as e:
        msg = str(e)
        if requested_device_type == "cuda" and ("CUDA error" in msg or "device-side assert triggered" in msg):
            print("Uwaga: CUDA jest w blednym stanie. Przelaczam model na CPU. Zrestartuj kernel, aby wrocic na CUDA.")
            active_device = "cpu"
            active_device_type = "cpu"
            active_ptdtype = torch.float32
            model.eval().to(active_device)
        else:
            raise

    # --- encoder/decoder ---
    encode = None
    decode_token = None
    decode_ids = None
    dataset = checkpoint.get("config", {}).get("dataset")
    model_vocab_size = checkpoint.get("model_args", {}).get("vocab_size")
    if dataset:
        meta_path = os.path.join(ckpt_pkg_root, "data", dataset, "meta.pkl")
        if os.path.exists(meta_path):
            with open(meta_path, "rb") as f:
                meta = pickle.load(f)
            stoi, itos = meta["stoi"], meta["itos"]
            def encode(s: str) -> list[int]:
                return [stoi[c] for c in s]
            def decode_token(i: int) -> str:
                return itos[i]
            def decode_ids(ids: list[int]) -> str:
                return "".join(itos[i] for i in ids)
    if encode is None:
        if model_vocab_size not in (50257, 50304):
            raise FileNotFoundError(
                f"Nie znaleziono meta.pkl dla datasetu={dataset!r} (oczekiwano w {os.path.join(ckpt_pkg_root, 'data', str(dataset), 'meta.pkl')}). "
                f"Model ma vocab_size={model_vocab_size}, wiec fallback do tiktoken (GPT-2) bylby niepoprawny."
            )
        enc = tiktoken.get_encoding("gpt2")
        def encode(s: str) -> list[int]:
            return enc.encode(s, allowed_special={"<|endoftext|>"})
        def decode_token(i: int) -> str:
            return enc.decode([i])
        def decode_ids(ids: list[int]) -> str:
            return enc.decode(ids)
    return NanoGPTBundle(
        model=model,
        encode=encode,
        decode_token=decode_token,
        decode_ids=decode_ids,
        device=active_device,
        device_type=active_device_type,
        ptdtype=active_ptdtype,
    )

def last_token_probability_from_bundle(
    bundle: NanoGPTBundle,
    prompt: str,
    *,
    temperature: float = 1.0,
    top_k: Optional[int] = None,
):
    distribution = next_token_distribution_from_bundle(bundle, prompt[:-1], temperature=temperature, top_k=top_k)
    key = bundle.encode(prompt[-1])[0]
    return distribution[key][1]
prompt = "Pro"
print(next_token_distribution_from_bundle(bundle_proving,prompt,temperature=1))
random_next_token(bundle_proving, prompt, temperature=1.0, randomize=0.0, acceptable_tokens=['v','e'])
##%%
print("1","2")
##%%
def next_line(
    bundle: NanoGPTBundle,
    prompt: str,
    *,
    temperature: float = 1.0,
    temperature_begin_line : float = 10,
    multiplier_begin_line : float = 0.66666666,
    top_k: Optional[int] = None,
    is_first_proof_line = False
)->str:
    ans = prompt
    next_token = None
    if is_first_proof_line:
        next_token = "1"
        ans += next_token
    while next_token != "\n":
        next_token = random_next_token(bundle,ans,temperature=temperature)
        ans += next_token
    return ans.splitlines()[-1]def random_next_token(
    bundle: NanoGPTBundle,
    prompt: str,
    verbose: bool = False,
    temperature: float = 1.0,
    randomize: float = 0.0,
    acceptable_tokens=None,
):
    source = next_token_distribution_from_bundle(
        bundle,
        prompt,
        temperature=temperature
    )
    token_ids = source[:,0]
    probs = source[:,1]
    decoded_tokens = [bundle.decode_token(tok_id) for tok_id in token_ids]
    # filtrowanie po acceptable_tokens
    # jeśli acceptable_tokens is None albo zawiera None, to wszystko dozwolone
    if acceptable_tokens is not None and None not in acceptable_tokens:
        acceptable_tokens_set = set(acceptable_tokens)
        filtered = [
            (tok_id, prob, tok_str)
            for tok_id, prob, tok_str in zip(token_ids, probs, decoded_tokens)
            if tok_str in acceptable_tokens_set
        ]
        if len(filtered) == 0:
            raise ValueError("Żaden token nie pasuje do acceptable_tokens")
        token_ids = np.array([x[0] for x in filtered], dtype=int)
        probs = np.array([x[1] for x in filtered], dtype=float)
        decoded_tokens = [x[2] for x in filtered]
        prob_sum = probs.sum()
        if prob_sum <= 0:
            raise ValueError("Suma prawdopodobieństw po filtracji wynosi 0")
        probs = probs / prob_sum
    if verbose:
        verbose_table = []
        for tok_str, prob in zip(decoded_tokens, probs):
            verbose_table.append([tok_str, prob])
        verbose_table.sort(key=lambda x: x[1], reverse=True)
        for i in verbose_table[:10]:
            print(i)
    return bundle.decode_token(random.choices(token_ids, weights=probs)[0])@torch.no_grad()
def next_token_distribution_from_bundle(
    bundle: NanoGPTBundle,
    prompt: str,
    *,
    temperature: float = 1.0,
    top_k: Optional[int] = None,
) -> np.ndarray:
    x = torch.tensor(bundle.encode(prompt), dtype=torch.long, device=bundle.device)[None, :]
    with torch.autocast(
        device_type=bundle.device_type,
        dtype=bundle.ptdtype,
        enabled=(bundle.device_type == "cuda" and bundle.ptdtype != torch.float32),
    ):
        logits, _ = bundle.model(x)

    # logits: [1, T, V]
    next_logits = logits[0, -1, :] / temperature
    if top_k is not None:
        values, indices = torch.topk(next_logits, top_k)
        probs = torch.softmax(values, dim=-1)  # <-- TU powstają prawdopodobieństwa (dla top_k)
        return np.array([(int(i), float(p)) for i, p in zip(indices, probs)], dtype=float)
    probs = torch.softmax(next_logits, dim=-1)  # <-- TU powstają prawdopodobieństwa (dla całego vocab)
    return np.array([(int(i), float(probs[i])) for i in range(probs.shape[0])], dtype=float)