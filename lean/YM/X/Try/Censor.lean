import YM.X.Try.Crease
import YM.X.Rank.Cash
/-!
# parity even through horizon 6 lives in all-pairs. and parity nc unit below. This allows comparing provisional non-H ℒ to H without commuting footprint balls or assuming rank of tomography after orientation-noncommuting CTs.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Maxwell Maxwell.Free Wick Next.Rank Normal LiftMark MvPolynomial Function Set Filter
open PertExtension
open Heat.Top hiding degree
open Pert Pert.Position Pert.RawLabels
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{d n k:ℕ}(F:Labels.Frames G) (h:G.Simple)
local notation "M"=> (Model F)
local notation "P"=> WickPol G
lemma address_en (x:Labels.Label G d): address F d (enroll F d x)= reduceEq x.val:= by change reduceEq ((F.level d).coords.symm ((F.level d).coords x)).val = _; rw [(F.level d).coords.symm_apply_apply]
lemma address_par (x:E F d): address F d (par F d x)=LiftMark.factors (-1) (address F d x):= by
    let p:= physicalLabel F d x; let B:=F.level d; have he (q:Labels.Label G d): address F d (par F d (enroll F d q))=reduceEq (scaledPol (F.level d) sign q).val:= by rw [par,scalePol_enroll,address_en]
    rw [← show enroll F d p=x from physical_round ..,he,address_en]; rw [← B.basis.sum_repr p]; simp_rw [map_sum, AddSubmonoidClass.coe_finsetSum, map_smul, map_sum,Submodule.coe_smul_of_tower,map_smul]; apply Finset.sum_congr rfl; intro i _; rw [scalePol_pure F _ _ (B.pure i)] -- may `B`
    let q:=B.basis i; let v:=reduceEq q.val; let k:= (B.grades i).2; have hh:HC v k:= by
       unfold v; apply Grow.hom_feed (F:=reduceEq) (u:=fun _=>1) -- name
       · intro i; exact reduce_grade (fun _:ℕ=>1) i
       exact labelHC _ (B.pure i)
    rw [Submodule.coe_smul_of_tower,map_smul]; apply congr_arg; change (-1:ℂ)^k • v=factors _ v; exact Eq.symm (by nth_rw 1 [← leafy.mp hh]; rw [factor_cut, leafy.mp hh])
include h in
lemma even_four (x:E F 4): par F 4 x=x:= by
    apply address_inj F; rw [address_par]
    have he:= address_in F 4 x; rw [low_support h] at he
    set p:= address F 4 x with hp
    let S:=LinearMap.ker ((factors (V:=Maxwell.Slot G) (-1)).toLinearMap-LinearMap.id)
    have hh0: BottomOnly G ≤ S:= by apply Submodule.span_le.mpr; rintro a hv; obtain rfl:a=1:=hv; apply sub_eq_zero.mpr; exact map_one (factors _)
    have hu : Teams G 0 0 ≤ S:= by
        apply Submodule.span_le.mpr; rintro z ⟨p,q,rfl⟩; apply sub_eq_zero.mpr; change factors (V:=Maxwell.Slot G) (-1) _ = (team G p q); unfold team; rw [map_sum]; apply Finset.sum_congr rfl; intro i hi; rw [map_mul]; have hz (v:Flavor 0): factors (V:=Maxwell.Slot G) (-1) (bit v i)=(-1:ℂ) • bit v i:= by
            unfold bit symbol; simp only [map_sum,C_mul',map_smul,factors_X]; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i hi=> smul_comm .. -- symbol C multiply
        rw [hz,hz]; simp
    have hh:p∈S:= sup_le hh0 hu he
    apply sub_eq_zero.mp; exact hh
-- all pairs unrestricted even. Convenient beyond rank4
abbrev forest (G:Gauge):= {x: WickPol G|∃ p q:Rank.Style,x=team G (Rank.ax p.1 p.2) (Rank.ax q.1 q.2)}
def Paths (G:Gauge) := BottomOnly G ⊔ Submodule.span ℂ (forest G)
set_option maxHeartbeats 400000 in
lemma track_team (j l:ℕ) : Teams G j l≤ Paths G:= by
    refine le_trans (b:=Submodule.span ℂ (forest G)) ?_ le_sup_right; apply Submodule.span_le.mpr; rintro x ⟨p,q,rfl⟩; rw [SetLike.mem_coe]; let H:= Submodule.span ℂ (forest G); let L:=duetL G j l; rw [show team G p q=L p q from rfl, ← (Rank.ax j).sum_repr p, ← (Rank.ax l).sum_repr q]; simp_rw [map_sum,LinearMap.sum_apply]; apply (H.sum_mem); intro k _; apply H.sum_mem; intro i _; simp_rw [map_smul,LinearMap.smul_apply]; exact Submodule.smul_of_tower_mem H _ (Submodule.smul_of_tower_mem H _ (Submodule.subset_span (show (team G (Rank.ax j i) (Rank.ax l k)) ∈ forest G from ⟨⟨j,i⟩,⟨l,k⟩,rfl⟩))) -- name
lemma primary_six (x:Maxwell.Slot G→₀ℕ)(hc:Maxwell.Free.degree x ≤ 6) : Heat.Top.degree x≤ 3:= by
    suffices h: 2* Heat.Top.degree x ≤ Maxwell.Free.degree x by omega
    rw [Heat.Top.degree_eq,Maxwell.Free.degree,Finsupp.weight_apply,Finsupp.sum,Finsupp.sum,Finset.mul_sum]; apply Finset.sum_le_sum; intro i hi; unfold scaleW; change _ ≤ x i * (i.1+2); nlinarith
include h
lemma variant (x y:Maxwell.Slot G): moyenne G ((MvPolynomial.X x) * MvPolynomial.X y)∈ Paths G:= by
    rw [← symbol_coordinate x,← symbol_coordinate y]; simp_rw [divide,Finset.sum_mul,Finset.mul_sum,map_sum]; apply Submodule.sum_mem; intro i _; apply Submodule.sum_mem; intro j _; obtain ⟨v,hv⟩:= duet (flavor_pick (coordinateLeg x) _) (flavor_pick (coordinateLeg y) _) i j h; rw [hv]; exact Submodule.smul_of_tower_mem _ _ (track_team x.1 y.1 (in_team G _ _)) -- scalar complex?
lemma forests (p:P)(he:p∈shellSector G 6)(hx:factors (-1) p=p): p∈ Paths G:= by
    obtain ⟨he,hp⟩:= sector.mp he; rw [← paints_self hp,p.as_sum,map_sum]; apply (Paths G).sum_mem; intro i hi; let k:= Heat.Top.degree i; have h3:k≤3:= primary_six _ ((mem_restrictSupport_iff ℂ).mp he hi); have hE:(-1:ℂ)^k=1:= by
       have hv := congr_arg (coeff i) hx; rw [factors,Perch.jets_coeff] at hv; exact mul_right_cancel₀ (mem_support_iff.mp hi) (hv.trans (one_mul _).symm)
    rw [show MvPolynomial.monomial i (coeff i p) = coeff i p • MvPolynomial.monomial i 1 from (by rw [←map_smul,smul_eq_mul,mul_one]),map_smul]; apply Submodule.smul_mem; obtain ⟨v,hv⟩:= Common.letter i; rw [hv]; have he : (k=0∨k=2):= by interval_cases k <;> first | tauto | norm_num at hE
    generalize hg:i.sum (fun _ k=> k)=a at v hv ⊢; have he' : a=k:= (Heat.Top.degree_eq i|>.trans hg).symm; rcases he with he|he <;> rw [he] at he' <;> clear hg <;> subst a; · rw [glyphs,Fin.prod_univ_zero, paints_self (p:=1) (fun _=>map_one _)]; exact (le_sup_left (b:=Submodule.span ℂ (forest G))) (unit_mem G)
    rw [glyphs,Fin.prod_univ_two];exact variant h _ _
end YM.PositionX.Tri
