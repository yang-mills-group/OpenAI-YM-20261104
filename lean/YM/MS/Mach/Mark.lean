import YM.MS.Lifting.Brand
import YM.MS.Mach.Plate

set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Pilot Garment Color Book Convolve
open Motif Literal Halo Native Detect Lifting
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {k n:ℕ} {b:Bool} {z:ℂ} {F:Rack G n} {Y:Mield G n}
namespace Pole
variable (k) (f:Fin k→Plaq) (σ:Grid G k)
abbrev wing (k:ℕ) (f:Fin k→Plaq) (σ:Grid G k)(z:ℂ) : Mob G:= fun n=> prodS ℂ ( bite n G ) (coin 1) k (fun i:Fin k=> Pole_leaf z (f i) (σ i)) -- Pose phase.L.
lemma prepared : Safe (wing k f σ z n) z:= by
   induction k with| zero=> exact Safe.free 1| succ k ih=> exact (Pole.guarded (f 0).i (f 0).j (f 0).jets (σ 0)).lipP (ih (f∘Fin.succ) (σ∘Fin.succ))
def Grit (i:Plaq): ℕ:= 2+i.jets.length
def wage (k:ℕ)(f:Fin k→ Plaq): ℕ := ∑ i:Fin k,Grit (f i)
lemma wage_add (f:Fin (k+1)→Plaq): wage (k+1) f= Grit (f 0)+ wage k (f∘Fin.succ):= Fin.sum_univ_succ (fun i=> Grit (f i))
def LAMP (G:Gauge): Mob G→ₗ[ℂ] Mob G→ₗ[ℂ] Mob G:= LinearMap.mk₂ ℂ (fun X Y n=> bite n G (X n) (Y n)) (fun a b c=> funext fun n=>LinearMap.congr_fun (map_add (bite n G) (a n) (b n)) ( c n )) (fun s a b=>funext fun n=>LinearMap.congr_fun ( map_smul _ s ( a n )) ( b n )) (fun a b c=> funext fun n=> map_add (bite n G (a n)) ( b n) (c n)) (fun a b c=> funext fun n=> map_smul (bite n G (b n)) a (c n)) -- b a swapped
lemma pol_here (f:Plaq)(a:G.ColorIndex) : Present (E:=Mob G) (fun z n=> Pole G n f.i f.j z f.jets a):= by
   let P: Sky G→ₗ[ℂ] Mob G:={ toFun F n:= F n a,map_add':= fun _ _=>rfl,map_smul':=fun _ _ =>rfl}; exact (Pole.mood f.i f.j f.jets G).grows P
lemma Presence : Present (wing k f σ):= by
    induction k with| zero=> exact Present.here (E:=Mob G) (fun _:ℕ=> coin (1:ℂ))| succ k ih=> exact (pol_here (f 0) (σ 0)).pair (ih (f ∘ Fin.succ) (σ ∘ Fin.succ)) (LAMP G)
lemma radiant (u:G.El): repeatC u (wing k f σ z n)=∑ i:Grid G k,(Lifting.ink u i σ:ℂ) • wing k f i z n:= by
    unfold wing; rw [ prod_color (P:=repeatC u) (he:= glob_prod u) (h:=Safe.cpig (n:=n) _ _) ]; simp_rw [ comp_def, Pole_leaf, show ∀ (a:Plaq) i, repeatC u ( Pole G n a.i a.j z a.jets i)=_ from fun a i=> (Pole.ingot a.i a.j a.jets).1 u i ]; exact color_expand (bite n G) (coin 1) k (fun i=> Pole_leaf z (f i) ) u σ -- name w variables depend λ
abbrev saint (k:ℕ)(f:Fin k→Plaq)(σ:Grid G k) (z:ℂ): Mob G:= ∑ i:Grid G k,(Lifting.group G i σ:ℂ) • wing k f i z
end Pole
end YM.MS.Mach
