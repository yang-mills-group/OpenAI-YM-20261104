import YM.RegulatorIR.Axial.Wane
import YM.RegulatorIR.Gain.Lyre

/-!
# Compact support with *same finite* moving packet
No implicit equality imposed across deck coils; evaluate after exact copies.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Axial
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight PowerSeries Gain Prim Motion Budget.Packet Budget.Deck
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries
variable {I J:Type}[Fintype J]{G:Gauge} {r k:ℕ}
variable {p:Signed} {f:Side}

lemma compact_eval (y:I→PowerSeries ℝ)(T:Packet I r) (b:J→I)(hb:Injective b)(hs:Function.support y⊆Set.range b): rhyme y T k= ∑ x:Tuple J r,T (b∘x)*coeff k (pip (y∘b) x):=by
 let F(x:Tuple J r):Tuple I r:= b∘x
 have hf: Injective F:=fun i j h=> funext fun l=>hb (congr_fun h l)
 unfold rhyme;let u(x:Tuple I r):=T x*coeff k (pip y x)
 have hm : Function.support u⊆ Set.range F:=by
    intro x h; have ht(j: Fin r): y (x j)≠0:=fun hh=>h (by
       have hh: pip y x=0:= Finset.prod_eq_zero (Finset.mem_univ j) hh
       unfold u; rw [hh,map_zero,mul_zero]); choose f hF using (fun j=> hs (ht j)); exact ⟨f,funext hF⟩
 rw [← hf.tsum_eq hm,tsum_fintype]; rfl

-- W1 shadow, eventually exact
abbrev medal (S:Finset (Edge Cover)) (G:Gauge):= ↥S × G.ColorIndex
def wire (S:Finset (Edge Cover))(u:medal S G): Foot G:=(u.1.val,u.2)

structure Brief (p:Signed) (f:Side) (X:(z:Side)→ ℝ → Horizon G (rep f z)) (a: Foot G→PowerSeries ℝ) where
 stampK : Finset (Edge Cover)
 suited : Function.support a⊆ Set.range (wire stampK)
 sky : ∀ᶠ z:Side in atTop, ContDiffAt ℝ ∞ (X z) 0
 endQ : ∀ᶠ z:Side in atTop, Function.support (vow (peel (X z))) ⊆ Set.range (fun i: medal stampK G=> (sig p f z (wire stampK i).1,(wire stampK i).2))
 pays : ∀ᶠ z:Side in atTop,∀ i:medal stampK G,let u:= wire stampK i; tale (fun t=>fire (X z t) (secure p f z u.1) u.2)=a u
namespace Brief
variable {X:(z:Side)→ℝ → Horizon G (rep f z)} {a:Foot G→ PowerSeries ℝ} (F:Brief p f X a)
variable {l P:ℝ}(h:Even f.val)(hp:l*f.val=P)(he:4≤ f.val)
local notation "D" => Carto G l P h hp
local notation "Q" => fun z=> playS (G:=G) (Sight.slab z) h hp
local notation "O" => medal F.stampK G
include F
lemma legible : ∀ᶠ z:Side in atTop,∀ u: O, let x:= wire F.stampK u; let y:=(D).wind (spark p z) x; chord (Q z) (vow (peel (X z))) y=a x:=by
 filter_upwards [F.sky,F.pays] with z hz hg u x y
 specialize hg u
 rw [chord_s _ _ (Ward.RangeR.lifts hz)]; unfold vow; apply Eq.trans _ hg
 let c:= (Q z)
 apply congr_arg; ext1 v; refine firebrand (h.mul_left _) (show l* (rep f z).val= ((Sight.slab z).val:ℝ)*P from ?_) (X z v) _ _
 rw [Gain.rep, PNat.mul_coe,Nat.cast_mul, mul_left_comm, hp]
include he
lemma owns {T:Packet (Foot G) r} (H: (Carto G l P h hp).Ready T)(i:Fin r)(hm:∀ q:Foot G,Summable fun x: Hold i q=> ‖T x.val‖):
 Tendsto (fun z=>rhyme (vow (peel (X z))) ((playS (Sight.slab z) h hp).deckSum T) k) atTop (𝓝 (rhyme a T k)):=by
 let v:O→ Foot G:=wire F.stampK
 have hv: Injective v:= fun i j hh=> Prod.ext (Subtype.ext (congr_arg Prod.fst hh)) (congr_arg (fun i:Foot G=>i.2) hh)
 let b(z:Side):Foot G→ Foot G:=(D).wind (spark p z); let Y(z:Side):= (Q z).orbit ∘ b z ∘ v
 let c(z:Side)(q:Tuple O r) := let y:= b z ∘ v ∘ q; (Q z).polish y*(Q z).deckSum T ((Q z).project y)*coeff k (pip (a ∘ v) q)
 have hl : Tendsto (fun z=>∑ q:Tuple O r,c z q) atTop (𝓝 (rhyme a T k)):=by
    rw [compact_eval a T v hv F.suited]; exact tendsto_finsetSum _ fun i' _ => (melted p f h hp he T H (v ∘ i') i (hm ((v ∘ i') i))).mul_const _
 have hh : ∀ᶠ z:Side in atTop,Injective (Y z):=by
    refine eventually_all.mpr fun i=>eventually_all.mpr fun j=>?_
    exact (clear p f h hp he (v i) (v j)).mono fun z hz h=> hv (hz h)
 apply hl.congr'; filter_upwards [hh,F.endQ,F.legible h hp] with z hz ht he
 let V:= vow (peel (X z));let L:= (Q z)
 have hp:Function.support V⊆Set.range (Y z):= ht
 rw [compact_eval _ (L.deckSum T) (Y z) hz hp]; apply Finset.sum_congr rfl; intro x _
 let y:= b z ∘ v ∘ x; let q:= Y z∘x;let l:=L.polish y;let L':=pip (a ∘ v) x
 have hm : L'=PowerSeries.C l * pip V q:=by
    rw [show L'=pip (chord L V) y from ?_,chord_p]; rfl
    unfold L' pip;apply Finset.prod_congr rfl; intro i _; exact Eq.symm (he (x i))
 change l*L.deckSum T (L.project y)*coeff k L'=L.deckSum T (L.project y)*coeff k (pip _ x)
 rw [hm,coeff_C_mul, show pip (V ∘ Y z) x=pip V q from rfl]; have he:l*l=1:= L.polish_sq y; change l*L.deckSum T _*(l*coeff k (pip V q))= L.deckSum T (L.project y)*coeff k (pip V q); linear_combination L.deckSum T (L.project y)*coeff k (pip V q)*he
end Brief
end YM.RegulatorIR.Axial
