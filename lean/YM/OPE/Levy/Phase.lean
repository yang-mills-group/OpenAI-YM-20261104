import YM.OPE.Levy.Boxes
import YM.OPE.Short.Leading

/-!
# Zeroth channel of the separated nonperturbative OPE on the weak frames

Insert exact station fields before applying the hierarchy products and then
compare against the (regular) separated Maxwell-Wick kernel. All phases,
uniform on separated-shape boxes at each arity. This needs the new matching
of engineering costs on one curve, not a subpower normalization cost assumed
from every `FirstExtension`. Not positive perturbative orders.
-/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.OPE.Levy
open Filter Set Function Table Ward Orbits Nesting Extraction Climb Next.UVStress Spec
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (X:Scaling S) (H:Anchored U.sector.derivatives (path X) (isoPanel X)) (h₀:Services C F S)
local notation "Q" =>U.sector.derivatives
local notation "T" =>zstamp (path X)
local notation "A" =>X.U
local notation "r" =>X.r
local notation "targetFree" =>Maxwell.freeTable C.labels
variable {I:Type}[Fintype I]{d:I→ℕ}(v:(i:I)→(Bel C.book).Field (d i))
variable {M η:ℝ}(hM:0 ≤ M)(hη:0 < η)
local notation "positions" k x o=> Short.harmonic ((X).r k) x o
-- suppression of all stress flags: even when a label actually agrees with a component in the free theory, use its moving field.
def testedWord (k:ℕ)(x:I→E4)(o:E4)(q:Viewers U):ℂ := Orbits.moment (spectator U q) (Short.harmonic (X.r k) x o) (primary X d v k)
def freeSlots (x:I→E4):ℂ:=Orbits.moment targetFree x (v)
def testedZero (k:ℕ)(x:I→E4)(o:E4):ℂ:=Short.scalar U R (Short.harmonic (X.r k) x o) (fun i=>⟨d i,primary X d v k i⟩) o

lemma beta (a:ℝ)(ha:0<a): Tendsto (fun k=>Real.exp (-a*T k)) atTop (𝓝 0):=
     Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr ha) (zlarge (path X)))

include hη X
lemma assign_pred (Y:Pert.FirstExtension U X)(ε:ℝ)(he:0<ε):∀ᶠ k in atTop, ∀ x∈ Short.plate I M η,∀ o:E4,
            ‖testedWord U X v k x o none-freeSlots v x‖ ≤ ε:=by
     let vT : Fin (Fintype.card I)→ (Bel C.book).Tag := Orbits.tags v ∘ runNames I
     have hZ:=Y.jets _ 0 vT (fun _=>false) 0 (K:=Short.frame '' Short.plate I M η)
                  ((Short.meal I M η).image Short.framed.continuous)
                  (Set.image_subset_iff.mpr (fun i hi=> Short.occupancy _ (Short.plate_conf hη _ hi))) he
     let B(k):=Orbits.tags (primary X d v k) ∘ runNames I
     let f(k:ℕ)(x:Points (Fintype.card I)):=disc (B k) (X.r k • x)
     let g:=disc vT
     filter_upwards [hZ] with k hk x hx o
     have hf:(fun z => disc (Pert.scaledPhysical X U.sector.energy k vT (fun _=>false) 0) (X.r k • z))=f k := by
       unfold f B; rfl
     specialize hk _ (Set.mem_image_of_mem Short.frame hx)
     rw [hf,show disc (Pert.freeWithStress C.labels vT (fun _=>false) 0)=g from rfl,show iteratedFDeriv ℝ 0 .. - iteratedFDeriv _ _ _ _=iteratedFDeriv ℝ 0 (f k-g) (Short.frame x) by ext; simp] at hk -- ext not funext?
     rw [norm_iteratedFDeriv_zero,Pi.sub_apply] at hk
     convert hk using 1
     have ht: testedWord U X v k x o none=f k (Short.frame x):=by
       let x':=fun i=>X.r k • x i
       let w:=primary X d v k
       unfold testedWord Short.harmonic
       exact (Orbits.carrying (a:=(primary X d v k)) (S:=S) U.room.kernel (show Injective x' from (smul_right_injective E4 (X.positive k).ne').comp (Short.plate_conf hη _ hx)) o).trans rfl
     rw [ht]; rfl

include H R h₀
lemma consistent(g:G.Simple)(Y:Pert.FirstExtension U X)(ε:ℝ)(he:0<ε):∀ᶠ k in atTop,∀ x ∈ Short.plate I M η, ∀ (o:E4)(q:Viewers U), ‖testedZero U R X v k x o - freeSlots v x‖ ≤ ε ∧ ‖testedWord U X v k x o q - freeSlots v x‖ ≤ ε :=by
       let w:Empty→S.Tag:=fun z=>Short.extra (S:=S) (z:=z)
       let δ:= ε/4
       have hp : 0<δ := div_pos he (by norm_num)
       have hβ:= (beta X (1/2) (by norm_num)).eventually (gt_mem_nhds hp)
       have hw:=Levy.uniform (U:=U) (M:=M) (η:=η) (δ:=1) R X H h₀ hη zero_lt_one v (voices w) 0 (-(1/2:ℝ)) (show -((0:ℕ)+1:ℝ)< -(1/2:ℝ) from by norm_num)
       filter_upwards [assign_pred U X v (M:=M) hη Y δ hp, hβ,hw] with k hf hβ hw x hx o q
       let x':=Short.harmonic (X.r k) x o
       let v'(i:I):S.Tag:=⟨d i,(primary X d v k) i⟩
       have hcl:ClearOf o Short.gapPos 1:= ⟨(fun i=>nomatch i),(fun i=>nomatch i)⟩
       have hΔ(q) := Short.identity_formula U R X g x' v' o q (Short.injective_harmonic X hη _ _ hx k)
       have hz(q:Viewers U): ‖testedWord U X v k x o q - testedZero U R X v k x o‖ ≤ δ :=by
          specialize hw q x' o Short.gapPos (Short.fitted hη (X.positive k).le x o hx) hcl
          change ‖Orbits.balance U (spectator U q) R 0 x' o (voices v') Short.gapPos (voices w)‖ ≤ _ at hw
          rw [Orbits.tested_fields,← Orbits.formula, hΔ q] at hw
          apply le_trans hw (show Real.exp _ ≤ δ from hβ.le)
       have h1:‖testedZero U R X v k x o - freeSlots v x‖ ≤ 2*δ:=by
            apply (norm_sub_le_norm_sub_add_norm_sub _ (testedWord U X v k x o none) _).trans; rw [two_mul,norm_sub_rev (testedZero ..)]; exact add_le_add (hz _) (hf _ hx _)
       have ht:ε=4*δ:=by unfold δ; field_simp
       rw [ht]; exact ⟨h1.trans (by linarith only [hp]),(norm_sub_le_norm_sub_add_norm_sub _ (testedZero U R X v k x o) _).trans ((add_le_add (hz _) h1).trans (by linarith only [hp]))⟩

end YM.OPE.Levy
