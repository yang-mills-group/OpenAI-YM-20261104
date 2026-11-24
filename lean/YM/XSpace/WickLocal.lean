import YM.XSpace.InfiniteK
import YM.XSpace.Stencils
import YM.Next.RANK.GaussTrack
import YM.Next.RANK.SpectrumReal
/-!
# Cover Wick algebra modulo Bianchi

Linear realized Address polynomials; no assumption of free independence
before the on-shell read. Proof uses Gaussian *translations*, even
at real precolored classical backgrounds, through auxiliaries of varying
period, not requiring rank uniformity at all.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace
open Function Set Filter Lattice Wilson MeasureTheory Laurent Bloch Exterior Matrix Source
open Next.Free Precision PhysicalNext.RankCovariance Further.FreeCovariance.KP
open Further.CorrectedLift Next.Rank Normal Spindle MvPolynomial
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators ContDiff
section heat
variable {V Z α : Type*} {H : Filter α} (K : α→Symmetric V) (Q : Symmetric V)
variable (M : α→ V→ℂ) (m : V→ℂ)
variable (hK : ∀ i j,Tendsto (fun a=>(K a).cov i j) H (𝓝 (Q.cov i j)))
variable (hm : ∀ i,Tendsto (fun a=>M a i) H (𝓝 (m i)))
include hK hm
lemma Wick_crosses [DecidableEq Z] (f : Z → V) (F : Finset Z) : Tendsto (fun a=> Normal.blend (K a) (M a) (glyphs f F)) H (𝓝 (Normal.blend Q m (glyphs f F))) := by
  classical
  induction F using Finset.strongInduction with
  | H F ih =>
    rcases eq_or_ne F ∅ with hg|hg
    · simp [hg]; exact tendsto_const_nhds
    obtain ⟨w,hw⟩:= Finset.nonempty_iff_ne_empty.mpr hg
    let B:= F.erase w
    have he : w∉B := Finset.notMem_erase _ _
    have hF : F=insert w B:= (Finset.insert_erase hw).symm
    have hx:B ⊂ F := Finset.erase_ssubset hw
    rw [hF]; simp_rw [Normal.spring _ _ _ _ he]
    refine ((hm _).mul (ih _ hx)).add (tendsto_finsetSum _ fun j _=> ?_)
    exact (hK (f w) (f j)).mul (ih _ (Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) hx))
lemma Wick_tendsto (p : poly V) : Tendsto (fun a=> Normal.blend (K a) (M a) p) H (𝓝 (Normal.blend Q m p)) := by
  classical
  -- recurse via writing a sum of monomials
  rw [p.as_sum]; simp only [map_sum, monomial_eq,C_mul',map_smul]
  apply tendsto_finsetSum; intro d hd
  apply Tendsto.const_smul
  let A:= (v : d.support) × Fin (d v.val)
  let z (i:A) := i.1.val
  have he : d.prod (fun i l=> (X i:poly V)^l)=glyphs z Finset.univ := by
    rw [Finsupp.prod,← Finset.prod_attach,glyphs,Fintype.prod_sigma]
    simp only [z,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rfl
  simp_rw [he]; exact Wick_crosses K Q M m hK hm z _
end heat

variable (G : Gauge)

abbrev beats (n : Side) := complexK (kernel G n) (kernel_symm ..)
def closes (n : Side) (k : AKey G):FKey G n:= ((wrap n k.1,k.2.1),k.2.2)
def self (n : Side):=scope (fun i=> Finsupp.single (closes G n i) 1) (beats G n)

def local_cov (i j:AKey G):ℂ := if i.2.2=j.2.2 then
    Orb0 (plaquette i.2.1) (plaquette j.2.1) (i.1-j.1) else 0

lemma born_self (n : Side) (i j : AKey G) : (self G n).cov i j= if i.2.2=j.2.2 then
    orb0 n (plaquette i.2.1) (plaquette j.2.1) (i.1-j.1) else 0 := by
  unfold self; rw [Normal.match_name]; exact kernel_cover ..
lemma islands (i j : AKey G) : Tendsto (fun n=> (self G n).cov i j) atTop (𝓝 (local_cov G i j)) := by
  simp_rw [born_self, local_cov]; by_cases h:i.2.2=j.2.2
  · simp_rw [if_pos h]; exact orb0_to ..
  simp_rw [if_neg h]; exact tendsto_const_nhds

def WickK : Symmetric (AKey G) :=
  ⟨local_cov G,fun i j=> tendsto_nhds_unique_of_eventuallyEq (islands G i j) (islands G j i) (Eventually.of_forall fun n=> (self G n).symm ..)⟩
theorem real_WickK (i j : AKey G) : star ((WickK G).cov i j)=(WickK G).cov i j := by
  refine tendsto_nhds_unique_of_eventuallyEq (islands G i j|>.star) (islands G i j) (Eventually.of_forall fun n=>?_)
  dsimp only [self]; rw [Normal.match_name]; exact Complex.conj_ofReal _

section projection
variable (n : Side)
local notation "I" => FKey G n

def spreads (i:I) := ∑ j:I, Finsupp.single j (↑(kernel G n i j):ℂ)
lemma reproduces : scope (spreads G n) (beats G n)= beats G n := by
  apply Normal.Symmetric.ext; funext i j
  have hp : kernel G n * kernel G n * (kernel G n).transpose= kernel G n := by rw [projector,kernel_symm,projector]
  have he := congr_arg Complex.ofReal (congr_fun (congr_fun hp i) j)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,Complex.ofReal_sum,Complex.ofReal_mul] at he
  simp only [scope,treats,spreads,map_sum,Finsupp.linearCombination_single,Finset.sum_apply,Pi.smul_apply, beats,complexK,smul_eq_mul]; simp_rw [mul_comm (↑(kernel G n j _):ℂ)]; exact he

lemma reread (x : I→ℝ) (i): reads (spreads G n) (fun l=>(x l : ℂ)) i = (↑((kernel G n *ᵥ x) i):ℂ) := by
  simp only [Normal.reads,spreads,Matrix.mulVec,dotProduct,map_sum,Finsupp.linearCombination_single,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]

def periodic_heat (p : poly I) (A : Pot G n) := Normal.blend (beats G n) (fun i=> (fields G n A i : ℂ)) p
lemma reread_period (p q:poly I) (h : ∀ A, text (fields G n A) p=text (fields G n A) q) (A : Pot G n): periodic_heat G n p A= periodic_heat G n q A := by
  have hx : exchange (spreads G n) p=exchange (spreads G n) q := by
    apply audible; intro x
    obtain ⟨B,hB⟩:=project_into G n x
    have he : reads (spreads G n) (fun l=>(x l:ℂ)) =fun i=> (fields G n B i:ℂ) := _root_.funext fun i=> by rw [reread,hB]
    change aeval _ (exchange _ p)=aeval _ (exchange _ q); rw [reads_val,reads_val,he]; exact h B
  let V (i:I) := (fields G n A i:ℂ)
  have he : reads (spreads G n) V=V := _root_.funext fun i=> by unfold V; rw [reread,project_fixes]
  have hh := congr_arg (Normal.blend (beats G n) V) hx
  rw [wets,wets,reproduces,he] at hh; exact hh

-- lifting with exact plaquette wraps

def CoverC := Edge Cover→ G.Color

def curlC (A : CoverC G) (v : AKey G) := Exterior.linkSum A v.1 (square v.2.1.val.1 v.2.1.val.2) v.2.2

def ofCover (A : CoverC G) : Pot G n := fun x=> A (lift x.1,x.2)
def inCover (A : Pot G n) : CoverC G := fun x=> A (wrap n x.1,x.2)

lemma curl_addC (A : CoverC G) (x : Cover) (a : PA) (j : G.ColorIndex) : curlC G A (x,a,j)= (A (x,a.val.1)+A (x+step a.val.1,a.val.2)-A (x+step a.val.2,a.val.1)-A (x,a.val.2)) j := by
  unfold curlC
  simp only [square, linkSum,Step.used,posDir,negDir,Step.vec,↓reduceIte,Bool.false_eq_true, add_zero]
  rw [show x+step a.val.1+step a.val.2-step a.val.1=x+step a.val.2 by abel,show x+step a.val.1+step a.val.2+-step a.val.1=x+step a.val.2 by abel,add_sub_cancel_right]
  apply congr_arg (fun x:G.Color => x j)
  abel

lemma curl_inCover (A : Pot G n) (i : AKey G) : curlC G (inCover G n A) i = fields G n A (closes G n i) := by
  rcases i with ⟨x,a,j⟩
  rw [curl_addC]; simp only [inCover,map_add,wrap_step]; rfl
end projection
lemma intoCover (A : CoverC G) (i : AKey G) : ∀ᶠ n in atTop, fields G n (ofCover G n A) (closes G n i)=curlC G A i := by
  rcases i with ⟨x,a,j⟩
  filter_upwards [wraps_grow x, wraps_grow (x+step a.val.1), wraps_grow (x+step a.val.2)] with n hx hv hb
  rw [curl_addC]; simp only [fields,ofCover,closes, LinearMap.coe_mk,AddHom.coe_mk, field,curl,hx,← wrap_step n, ← map_add,hv,hb]

def local_heat (p : poly (AKey G)) (A : CoverC G) := Normal.blend (WickK G) (fun i=> (curlC G A i:ℂ)) p

lemma heat_lifts (p : poly (AKey G)) (A : CoverC G) :
    Tendsto (fun n=> periodic_heat G n (MvPolynomial.rename (closes G n) p) (ofCover G n A)) atTop (𝓝 (local_heat G p A)) := by
  simp_rw [periodic_heat,labelled, wets]; unfold local_heat
  apply Wick_tendsto _ _ _ _ (islands G) _ p; intro i
  refine (tendsto_const_nhds : Tendsto _ atTop (𝓝 (↑(curlC G A i):ℂ))).congr' ((intoCover G A i).mono fun n hn=>?_)
  simp [Normal.reads,hn]

-- Modulo vanishings on Bianchi. Deliberately *doesn't* work modulo stronger equation or stress-conservation quotient.
theorem heat_congr (p q: poly (AKey G)) (h : ∀ A:CoverC G, text (curlC G A) p=text (curlC G A) q) (A : CoverC G) : local_heat G p A=local_heat G q A := by
  refine tendsto_nhds_unique_of_eventuallyEq (heat_lifts G p A) (heat_lifts G q A) (Eventually.of_forall fun n=> reread_period G n _ _ (fun A=>?_) _)
  have he (P : poly (AKey G)) : text (fields G n A) (rename (closes G n) P) = text (curlC G (inCover G n A)) P := by
    apply DFunLike.congr_fun (f:=(aeval (fun l=>(fields G n A l:ℂ))).comp (rename (closes G n))); ext1 i; simp only [aeval_X,curl_inCover,AlgHom.comp_apply,rename_X]
  rw [he,he]; exact h _
end YM.XSpace
