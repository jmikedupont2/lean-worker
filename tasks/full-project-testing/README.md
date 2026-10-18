# Full Project Testing

## Commands

```bash
cd /home/mdupont/projects/lean-worker/minimal
./gokujo-fixed scan RequestProject
./gokujo-fixed check --json RequestProject
```

## Expected Results

- Scan completes without stack overflow
- Check returns exit code 0, Result: PASS
- No "Stack overflow detected" messages
