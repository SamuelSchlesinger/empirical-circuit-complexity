import Circuits.Basic

namespace Size3.Defs0

def f_0 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        false
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        false

def f_1 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        false
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true

def f_3 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true

def f_6 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        false
      else
        false

def f_7 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true

def f_15 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true

def f_22 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        true
      else
        false

def f_23 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        true
      else
        true

def f_24 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        false
      else
        false
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        true
      else
        false

def f_25 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        false
      else
        false
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        true
      else
        true

def f_27 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        false
    else
      if x ⟨2, by omega⟩ then
        true
      else
        true

def f_30 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        true
      else
        false

def f_60 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        true
      else
        false
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        true
      else
        false

def f_105 (x : Fin 3 → Bool) : Bool :=
  if x ⟨0, by omega⟩ then
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        false
      else
        true
    else
      if x ⟨2, by omega⟩ then
        true
      else
        false
  else
    if x ⟨1, by omega⟩ then
      if x ⟨2, by omega⟩ then
        true
      else
        false
    else
      if x ⟨2, by omega⟩ then
        false
      else
        true

end Size3.Defs0
