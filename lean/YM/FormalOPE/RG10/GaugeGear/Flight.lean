import YM.FormalOPE.RG10.GaugeGear.OnBoard
/-! # Unchanged rank tracking of conditional map

 Polynomial rank slicer.No physical horizon (mentions do NOT trivially include nothing). -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.GaugeGear
open HStein Route Route.Bulk MeasureTheory Function Finset
open MvPolynomial
open Multi.Vacuum.Gauss
open scoped Topology BigOperators Classical
variable {I B J : Type} [Fintype J]
local notation "Q"=> Packet (I⊕B)
local notation "X*"=> MvPolynomial.X
variable {e:Episode I B J} (q:I→ Row J) (w:I→Packet B) (P:Packet I) (p: Packet (I⊕ B)) (c:ℂ) (k:ℕ)
local notation "φ" => first e
local notation "V" => e.vertices
local notation "J*" => e.joint
local notation "L"=> Primitives.GCC.LocalPolynomial.length
local notation "H"=> MvPolynomial.homogeneousComponent
variable (i:Index I B)

lemma large (k:Letters I) : Finsupp.degree k=L k:= rfl
lemma sumL : L i=L (fine i)+L (Route.coarse i):= by
 unfold Primitives.GCC.LocalPolynomial.length; nth_rw 1 [sound i]; rw [Finsupp.sum_sumElim]; rfl
lemma types (h : P.IsHomogeneous k)(i:Letters I)(ht:i∈P.support): L i=k:= by -- name shadows i
 rw [← large]; have hh := h (MvPolynomial.mem_support_iff.mp ‹i∈P.support›);
 rw [Finsupp.degree_eq_weight_one]; exact hh
lemma hmul (h: P.IsHomogeneous k)(hw:∀ i,(w i).IsHomogeneous 1): (aeval w P).IsHomogeneous k:= by
 simpa using IsHomogeneous.aeval h w hw -- inspect
lemma flies : IsHomogeneous (hand q (glyph i)) (L (Route.coarse i)):= by
 rw [hand]; have he : MvPolynomial.support (glyph i)={i}:= by ext j; simp [glyph,MvPolynomial.mem_support_iff, coeff_monomial]; exact eq_comm -- inspect
 rw [he,sum_singleton]; exact (homogeneousSubmodule _ _ _).smul_mem _ ( (mem_homogeneousSubmodule ..).mpr (isHomogeneous_monomial _ (large _))) -- inspect

/-- Drop every fine letter. -/
def landing : Packet (I⊕B)→ₐ[ℂ] Packet B:= MvPolynomial.aeval (Sum.elim (0: I→Packet B) (fun b:B=> MvPolynomial.X b : B → Packet B)) -- annot

lemma lands_none (h : (fine i)=0) : hand q (glyph i)= landing (glyph i):= by
 apply all_conf;intro y; rw [hand_eq,lobby];
 have he(z:Row J): evaluate q y z (glyph i) = aeval y (landing (glyph i)):= by
    let f:=Sum.elim (0:I→ ℂ) y
    have hh : aeval y (landing (glyph i))= aeval f (glyph i):= by
      let R := (aeval (R:=ℂ) y).comp (landing (I:=I)); have hv : R = aeval f:= by
         ext (a|b); all_goals first | simp [R,f,landing] -- inspect
      change R _=_; rw [hv]
    rw [hh]; unfold evaluate glyph; simp only [aeval_monomial]; congr 1; unfold Finsupp.prod; apply prod_congr rfl; intro a ha
    cases a with
    | inr b=> rfl
    | inl a=> have ht := (fine_mem i a).2 ha; simp [h] at ht
 simp_rw [he, integral_const]; simp only [probReal_univ, one_smul] -- inspect
omit [Fintype J] in -- won't include by default? q not in view
lemma lands_zero (h : fine i≠0) : landing (glyph i)=0:= by
 have hu :(fine i).support.Nonempty:=  Finset.nonempty_iff_ne_empty.mpr (fun hi=>h (Finsupp.support_eq_empty.mp hi))
 obtain ⟨a,ha⟩:= hu; have hi:= (fine_mem i a).mp ha
 let u:= i-Finsupp.single (.inl a) 1
 rw [show i=u+Finsupp.single (.inl a) 1 from (Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)).symm, ← comma,call, landing,map_mul, aeval_X]; simp

-- project output n or greater; no covariance norms needed
lemma lands (p : Packet (I⊕B))(hp:p.IsHomogeneous k) {n:ℕ}(h:k≤n): H n (hand q p)= if k=n then landing p else 0 := by
 have hx (i:Index I B)(hi:i∈p.support): H n (hand q (glyph i))= if k=n then landing (glyph i) else 0 := by
    have hl:=types p k hp i hi; have h':=sumL i
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule ..).2 (flies q i))]; split_ifs with hu hv hv
    · have he : L (fine i)=0:=by omega
      exact lands_none q i ((Finsupp.degree_eq_zero_iff _).mp (Eq.trans (large _) he))
    · omega
    · rw [lands_zero i (fun hj=> hu (by rw [hj] at h'; change _=0+L _ at h'; omega))]
    rfl
 let S : Packet (I⊕B) →ₗ[ℂ] Packet B := { toFun:= hand q, map_add':=hand_sum q, map_smul':= fun _ a=>hand_times q a _ }
 change H n (S p)= _; rw [resolves p]; split_ifs with he
 · simp_rw [map_sum,map_smul]; apply sum_congr rfl;intro i hi; rw [show H n (S (glyph i)) = landing (glyph i) from (hx i hi).trans (if_pos he)];
 simp_rw [map_sum,map_smul]; exact sum_eq_zero (fun i hi=> by rw [show H n (S (glyph i))=0 from (hx i hi).trans (if_neg he), smul_zero])

def stamp (e:Episode I B J) : I→Packet B:= fun i=> landing (first e i)
omit [Fintype J] in
lemma landed (e:Episode I B J): landing (aeval (first e) P)=aeval (stamp e) P:= by
 let R:= landing.comp (aeval (R:=ℂ) (first e)); have h:R=aeval (stamp e):= by ext; simp [R,stamp]
 change R _= _; rw [h]

variable (H0:∀ i, (first e i).IsHomogeneous 1)
include H0 in
lemma repeated {n:ℕ}(h:k ≤ n)(hp:P.IsHomogeneous k): H n (beam e 0 P)= if k=n then aeval (stamp e) P else 0:= by rw [start, lands _ _ _ (hmul _ _ k hp H0) h, landed]
end YM.FormalOPE.RG10.GaugeGear
