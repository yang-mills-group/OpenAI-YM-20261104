import YM.Integration.WilsonIndependentMovingRosterStableRoots
import YM.Integration.WilsonIndependentMatchedRosterEdge

/-! The actual first connection of a finite mixed stable mask, with one
exterior on its own mesh. Changing the coarse angular ruler costs one
factor on the exterior. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterStableEdge

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile (Income)
open WilsonIndependentMovingRosterStableRoots (front)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n h e k u b i N:ℕ}{D:Fin (n+1)→ℕ}{E W:Credit}

theorem ruler {V:Era G ℝ}{x T A:ℝ}(x₀:0≤x)(zoom:1≤T)(bill:Flush e u (x/T) V A):
    Flush e u x V (T^u*A):=by
  have tp:0<T:=zero_lt_one.trans_le zoom
  have cost:0≤T^u:=pow_nonneg tp.le _
  refine ⟨mul_nonneg cost bill.1,?_⟩
  intro j hj r hr
  apply budget_minor (cap_scale (bill.2 j hj r hr) cost)
    (fun w=>mul_nonneg (hedge_nn x₀ _) (norm_nonneg _))
  intro w
  have step:hedge 0 x u w≤T^u*hedge 0 (x/T) u w:=by
    dsimp only [hedge,autumn]
    rw [←mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [mul_add,mul_one,←mul_assoc,show T*(x/T)=x from by field_simp]
    linarith only [zoom]
  calc
    _ ≤ (T^u*hedge 0 (x/T) u w)*‖V.2 j r w‖:=mul_le_mul_of_nonneg_right step (norm_nonneg _)
    _ = _:=mul_assoc ..

theorem original (R:Realm G (e+1) E)(sale:SpringD R k u b W)(live:R.anchor ≤ i)(edge:i < N)
    (l:Fin ((n+1)+1)→ℕ)(room:(∑s,l s) ≤ k)(φ:(s:Fin (n+1))→Rarity (D s))(ψ:Rarity h)
    (x y T gap zNear zFar:ℝ)(o:CellR)(x₀:0<x)(zoom:1≤T)(fit:x*(ll R.draws i).L.val≤1)(apart:0<gap)
    (same:∀s j,s≠j→ClearDay (φ s) (φ j) gap)
    (different:∀s,∀p∈tsupport (φ s).ψ.val,∀q∈tsupport ψ.ψ.val,gap≤dist p (T • q))
    (nearBox:∀s,radiusH (φ s) (x*(ll R.draws i).L.val) y≤zNear)
    (farBox:radiusH ψ ((x/T)*(ll R.draws i).L.val) (y/T)≤zFar)
    (nearLive:∀s,(VisitsT (φ s) x y o).Nonempty)(farLive:(VisitsT ψ (x/T) (y/T) o).Nonempty)
    (Y:Fin ((n+1)+1)→Era G ℝ)(A:Fin ((n+1)+1)→ℝ):
    let P:=ll R.draws i
    let roots:=front P φ ψ x y T o
    let η:=x*P.L.val
    let amounts:=Fin.cons (α:=fun _=>ℝ) (T^u*A 0) (Fin.tail A)
    let weight:=fun s=>pearlB u b (4*max zNear (T*zFar)) (gap/η)*nuP (coinMat k e+1) (n+1) s
    (∀s,Income (Y s) (l s) e (u+b) (fun a=>roots s (parentC P.L a)) (A s)) →
    (∀s,Flush e u (Fin.cons (α:=fun _=>ℝ) (η/T) (fun _:Fin (n+1)=>η) s)
      (verseI R.draws R.paid i N (l s) (Y s)) (A s)) →
    let joined:=DeltaGap R.draws R.paid i N Y l
    Auth (∑s,l s) joined ∧ Flush e u η joined
      ((n+1:ℕ)*R.cash (priceWG G e k u b E W) i*weight amounts):=by
  intro P roots η amounts weight fine coarse joined
  have split:=WilsonIndependentMovingRosterStableRoots.original P φ ψ x y T gap zNear zFar o
    x₀ zoom fit apart same different nearBox farBox nearLive farLive
  have ep:0<η:=mul_pos x₀ (by exact_mod_cast P.L.pos)
  let δ:=max 0 (δWarm R i (i+1))
  have δ₀:0≤δ:=le_max_left _ _
  have enlarged (s):A s≤amounts s:=by
    refine Fin.cases ?_ (fun _=>le_rfl) s
    exact le_mul_of_one_le_left (coarse 0).1 (one_le_pow₀ zoom)
  have goods (s):PaidMer e (u+b) (fun a=>roots s (parentC P.L a)) (Y s) (Y s) (amounts s) δ:=
    fun j r hj=>((fine s).2 δ δ₀ j r hj).stepX (enlarged s) δ₀
  have lower (s):Flush e u η (verseI R.draws R.paid i N (l s) (Y s)) (amounts s):=by
    refine Fin.cases ?_ (fun j=>coarse j.succ) s
    exact ruler ep.le zoom (coarse 0)
  have received (s):Fringed (l s) e u η (amounts s) δ
      (verseI R.draws R.paid i N (l s) (Y s)) (verseI R.draws R.paid i N (l s) (Y s)):=
    Fringed.same (lower s) (Auth.verse R.draws edge R.hG R.green (fine s).1) δ₀
  have globe:1≤4*max zNear (T*zFar):=
    (split 0 (Fin.succ (0:Fin (n+1))) ((Fin.succ_ne_zero _).symm)).globe
  have all:=drifted (n+1) Y Y l amounts roots globe (div_pos apart ep) room ep.le
    split sale live (Nat.lt_succ_self i) edge edge (le_max_right 0 _)
    (fun s=>(fine s).1) (fun s=>(fine s).1) goods received
  exact ⟨all.pen,by simpa only [weight,mul_assoc] using all.f_l⟩

end YM.Integration.WilsonIndependentMovingRosterStableEdge
