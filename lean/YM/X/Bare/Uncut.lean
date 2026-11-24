import YM.X.Bare.Born
import YM.X.Bare.Subcell
import YM.PertExtension.MaxwellReading
/-!
The unpositioned prescription (with SectionData.Sound/Bid.pop supplies fixed when applied).
Prior to coupling inversion.
Nested exact, orientation of the slot-count parity via the common normalized diagram expansion.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bare
open Pert Pert.Position PertExtension PertExtension.Chart Lattice Maxwell Maxwell.Free Labels Set Function Filter
open RG Wilson Source LatticePT Mixed
open scoped Topology BigOperators Classical
variable {G : Gauge} {F:Labels.Frames G} {d n : ℕ}

/-- Honest input Section choice. -/
structure Shop (F: Labels.Frames G) where
   H : Hol G
   S (d:ℕ) : SectionData (F.level d)
   hS (d:ℕ) : (S d).Sound H
   hP (d:ℕ) : Bid.pop (S d)
namespace Shop
variable (K:Shop F)
abbrev series (w:Fin n→LatticePT.Word G)(q:ℕ+)(k:ℕ)(t:Test n)(j:ℕ) : ℂ:= (polynomialTop w q k (Subcell.sweep (Complex.re ∘ t) (epsilon q k) ∘ points) j:ℂ)+Complex.I * (polynomialTop w q k (Subcell.sweep (Complex.im ∘ t) (epsilon q k) ∘ points) j:ℂ)
def full (q:ℕ+) (k d:ℕ) (t:Test n) (j:ℕ) := offspring F K.H K.S K.hS K.hP d (fun v=> series v q k t j)
def bank (q:ℕ+) (k d:ℕ) (j:ℕ) : Bank F d:= fun _ t=> adopt F K.H K.S K.hS K.hP d (fun v=> series v q k t j)
lemma bank_zoom (q:ℕ+)(k:ℕ) {e}(h:d≤e)(j:ℕ): pulls (up F h) (K.bank q k e j)=K.bank q k d j:= by funext n t; exact adopt_up F K.H K.S K.hS K.hP _ h

open Orb
local notation "V" => LatticePT.Word G
def bits (w:Fin n→ V) := ∑ i,((w i).F.grades (w i).axis).2
lemma dia_zero (q:ℕ+)(k:ℕ) : diagonalWith (tray G) (0:Observable G (side q k))=0:=by
   have ht : expectation (0:Observable G (side q k))=0 := by funext t; unfold expectation numerator entries; simp
   have he:= finite_formula (side_even q k) (traySpec G) (O:=0) ⟨continuous_const,contDiffAt_const⟩
   have hz:=PertExtension.Series.Tested.Aspiration.single (0:ℝ) 0; rw [show (fun r:ℝ=>r^(0:ℕ) • (0:ℝ))=0 from funext (by simp),show (fun i:ℕ=>if i=0 then (0:ℝ) else 0)= 0 from funext (by simp)] at hz
   rw [ht] at he; exact he.unique hz
lemma poly_odd (v:Fin n→ V)(q:ℕ+)(k:ℕ)(f:(Fin n→E4)→ℝ) {j:ℕ}(h:Odd (bits v+j)): polynomialTop v q k f j=0:= by
   refine Finset.sum_eq_zero fun p hp=> Finset.sum_eq_zero fun a ha=> Finset.sum_eq_zero fun b hb=> ?_
   refine mul_eq_zero_of_right _ ?_
   by_cases ho: Odd (number v b+j)
   · exact normalized_odd (traySpec G) (side_even q k) _ ho
   let NN(i:Fin n):=((v i).F.grades (b i)).2; let P(i:Fin n):=((v i).F.grades (v i).axis).2
   obtain ⟨i,hi⟩:∃ i,Odd (P i+NN i):= by
      by_contra! hx
      have hs:= Finset.even_sum (f:=fun i=> P i+NN i) (s:=Finset.univ) (fun i _=>Nat.not_odd_iff_even.mp (hx i)); rw [Finset.sum_add_distrib] at hs; change Even (bits v+number v b) at hs
      grind
   have hz (x): (v i).cost (b i) x=0:= by rw [LatticePT.Word.cost,even_slot (i:=(v i).axis) (j:=(b i)) _ _ _ _ hi, mul_zero]
   have H:placements v q k a p b=0:= funext (fun _=> Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz,zero_mul]))
   rw [H,show restrictedO (G:=G) 0=(0:Observable G (side q k)) from rfl,dia_zero];rfl
lemma sign_rule (v:Fin n→V)(q:ℕ+)(k:ℕ)(t:Test n)(j:ℕ): (-1)^bits v * series v q k t j=(-1)^j * series v q k t j:= by
   by_cases h:Odd (bits v+j)
   · simp only [series,poly_odd _ _ _ _ h,Complex.ofReal_zero,mul_zero,add_zero]
   rcases Nat.even_or_odd (bits v) with ha|ha
   · have hj : Even j:= by grind
     rw [ha.neg_pow,hj.neg_pow,one_pow,one_pow]
   · have hj : Odd j:= by grind
     rw [ha.neg_pow,hj.neg_pow,one_pow,one_pow]

lemma full_parity (q:ℕ+)(k:ℕ)(t:Test n)(j:ℕ) : (K.full q k d t j).compLinearMap (fun _=> scaledPol (F.level d) sign)=((-1:ℝ)^j • (K.full q k d t j)):= by
   refine Module.Basis.ext_multilinear (e:=fun _=> (F.level d).basis) fun p=>?_
   let B:=F.level d; let v: Fin n → B.Index:=p; let m:=born (d:=d) F K.H K.S K.hS K.hP; let P:=m ∘ p
   have he (i:B.Index): scaledPol B sign (B.basis i)=(-1:ℂ)^(B.grades i).2 • B.basis i := scalePol_pure F _ _ (B.pure i)
   let T:= K.full q k d t j
   have hr : T (B.basis ∘ v)=series P q k t j:= spread_eval ..
   rw [MultilinearMap.compLinearMap_apply,MultilinearMap.smul_apply]; change T (fun i=> scaledPol B sign (B.basis (v i))) = _ • T (B.basis ∘ v)
   simp_rw [he]; change T (fun i=>_ • (B.basis ∘ v) i)=_; rw [T.map_smul_univ (fun i=>(-1:ℂ)^(B.grades (v i)).2) (B.basis ∘ v)] -- defeq
   have hh : (∑ i:Fin n,(B.grades (v i)).2)=bits P:= Finset.sum_congr rfl fun i _=> congr_arg Prod.snd (base_grade F (v i)).symm
   rw [Finset.prod_pow_eq_pow_sum,hh,hr,smul_eq_mul,sign_rule]
   rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; change _ = (Complex.ofReal ((-1:ℝ)^j)) * _; simp

lemma bank_parity (q:ℕ+)(k:ℕ)(d j:ℕ): pulls (par F d) (K.bank q k d j)=(-1:ℝ)^j • K.bank q k d j:= by
    funext n t; ext1 p; let M:=K.full q k d t j; let L:=Pert.RawLabels.physicalLabel F d
    have he i : L (par F d (p i))= scaledPol (F.level d) sign (L (p i)):= scalePol_physical F sign _
    change M (fun i=> L (par F d (p i)))= ((-1:ℝ)^j • M) (fun i=> L (p i)); rw [show ((-1:ℝ)^j • M)=_ from (full_parity K q k t j).symm]; simp_rw [he]; rfl
end Shop
end YM.PositionX.Bare
