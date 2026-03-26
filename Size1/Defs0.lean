import Circuits.Basic

namespace Size1.Defs0

def f_0 (x : Fin 1 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    false
  else
    false

def f_1 (x : Fin 1 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    false
  else
    true

end Size1.Defs0
