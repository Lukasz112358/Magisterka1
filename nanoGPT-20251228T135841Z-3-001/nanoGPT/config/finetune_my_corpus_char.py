out_dir = 'out'
init_from = 'resume'

dataset = 'my_corpus_char'

# mniejszy LR na finetune
learning_rate = 2e-4
max_iters = 20000
lr_decay_iters = 20000
warmup_iters = 100

compile = False

always_save_checkpoint = True
eval_interval = 10