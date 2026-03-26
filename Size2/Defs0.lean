import Circuits.Basic

namespace Size2.Defs0

def f_0 (x : Fin 2 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      false
    else
      false
  else
    if x ⟨1, by omega⟩ then
      false
    else
      false

def f_1 (x : Fin 2 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      false
    else
      false
  else
    if x ⟨1, by omega⟩ then
      false
    else
      true

def f_3 (x : Fin 2 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      false
    else
      true
  else
    if x ⟨1, by omega⟩ then
      false
    else
      true

def f_6 (x : Fin 2 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      false
    else
      true
  else
    if x ⟨1, by omega⟩ then
      true
    else
      false

end Size2.Defs0
