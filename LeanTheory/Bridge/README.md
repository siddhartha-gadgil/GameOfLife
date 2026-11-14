# Bridge/

Composition theorems: they connect kernel laws to each other and to theory or certificate
results, with every hypothesis explicit, so that conclusions about one object can be combined.

- [`Example.lean`](Example.lean): `OscillatorLaw.shift` (time translation), `OscillatorLaw.add`
  and `OscillatorLaw.smul` (superposition), `energy_eq_of_law`, and `amplitude_bound`
  (conservation composed with the potential bound), used by `Certificates/Example`.
- [`LifeIO.lean`](LifeIO.lean): Game of Life exchange formats. `Snapshot` and `Evolution` with
  `Repr`, `ToJson` and `FromJson` instances, plaintext and RLE readers and printers, the
  checked `Evolution.valid`, computable `Snapshot.step`/`evolve` proved equal to the kernel
  evolution, and the pattern literals `rle% "…"` and `cells% "…"`. Data read from strings is
  untrusted; the module docstring states exactly which round trips are proved.
