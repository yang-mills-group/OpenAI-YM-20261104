import YM.X.Grow.Hue
import YM.X.Bare.Marks
/-!
# The Crace inverse pays exactly all weights. No appeal to perfect improvement, uses Tri on-shell restrict, proves B matrix solves in homogeneous coordinates.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bare
open Maxwell Maxwell.Free Lattice Wilson Pert PertExtension LatticePT Stems Function Filter MeasureTheory Metric Set
open Pert.Position Pert.RawLabels Next.Rank Normal MvPolynomial Labels Submodule Extra.FD Dial Grow LiftMark
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {d e k:ℕ} {V:Type*}[AddCommGroup V][Module ℂ V]{F:Labels.Frames G} (S:Shop F)
set_option quotPrecheck false
local notation "I" => (F.level d).Index
local notation "L" => Label G d
local notation "ℚₚ" => physicalJet G d
local notation "E" => Pert.Position.E F d
-- field-jet equiv static system. ℋ0.
def screen (F:Frames G) (d:ℕ) : Pert.Position.E F d →ₗ[ℂ] Book G:= beam d ∘ₗ physicalLabel F d
lemma screen_eval (F:Frames G)(x:L): screen F d (enroll F d x)=beam d x:= by rw [screen,LinearMap.comp_apply,embed_round,shine,shine];exact congr_arg _ (unchanged _)
lemma screen_range (F:Frames G)(d:ℕ) : LinearMap.range (screen F d)=physicalJet G d:= by
   rw [←beam_range]; apply le_antisymm; exact LinearMap.range_comp_le_range _ _
   rintro p ⟨x,rfl⟩; exact ⟨enroll F d x,screen_eval F x⟩
lemma screen_in (F:Frames G)(d:ℕ): Injective (screen F d):= by
   intro x y h; let X:= physicalLabel F d x; let Y:= physicalLabel F d y; have he:= congr_arg (lessJob (G:=G)) h; change lessJob (beam d X)= lessJob (beam d Y) at he; rw [shine,shine,strict,strict] at he; exact (physical_round F x) ▸ (physical_round F y) ▸ (enroll_eq F).mpr he

def alpha (d:ℕ): Label G d →ₗ[ℂ] Book G:= bloom d ∘ₗ self S d
def coreP (d:ℕ): Pert.Position.E F d →ₗ[ℂ] Book G:= alpha S d ∘ₗ physicalLabel F d

lemma alpha_name (i:I): level (vapor G) (wt F i) (alpha S d ((F.level d).basis i))=beam d ((F.level d).basis i):= by
    let w:=useWord S i; change level (vapor G) w.d (bloom d (self S d _))=_
    rw [self_name]; have he:= few_commute (n:=w.d) («E»:=Reed.Okay G) (Reed.valP (G:=G)) ((F.level d).bound i) (looking w)
    change _= layBox ((F.level d).basis i).val; rw [←base_weight_val S]; exact he.trans (bloom_word _)
lemma alpha_c (p:L): alpha S d p∈ℚₚ:= by rw [← (F.level d).basis.sum_repr p,map_sum]; apply Submodule.sum_mem; intro i _; rw [map_smul]; apply Submodule.smul_mem; change bloom d _ ∈_; change bloom d (self S d ((F.level d).basis i))∈ _; rw [self_name]; exact bloom_physical ..
include S in
lemma very (i:I): IsWeightedHomogeneous (vapor G) (beam d ((F.level d).basis i)) (wt F i) := by
    change IsWeightedHomogeneous (vapor G) (layBox ((F.level d).basis i).val) (useWord S i).d; rw [← base_weight_val S i]; exact hom_feed _ layBox_hom (pureR _)
lemma staunch (i:I): Strong (vapor G) (wt F i+1) (alpha S d ((F.level d).basis i)-beam d ((F.level d).basis i)) := by
    apply Strong.undo; rw [map_sub,alpha_name,trimmer_hom le_rfl (very S i),sub_self]
lemma hoist (i:I): Strong (vapor G) (wt F i) (alpha S d ((F.level d).basis i)):= by
    have h := ((staunch S i).weaken (Nat.le_succ (wt F i))).add (Strong.of_pure (very S i)); rwa [sub_add_cancel] at h

lemma core_in : Injective (coreP S d):= by
   apply LinearMap.ker_eq_bot.mp (le_antisymm _ bot_le); intro p hp
   let M:= F.level d; let x:= physicalLabel F d p; change alpha S d x=0 at hp; let f (i:I):= M.basis.repr x i; let b(i:I):= alpha S d (M.basis i); let race (i:I):= wt F i
   have hc (r:ℕ) (i:I)(hr:r=race i): f i=0:= by
      induction r using Nat.strong_induction_on generalizing i with
      | _ r IH=>
        let l : ℕ×ℕ→ℂ:= fun j=>if j.1=r then 1 else 0 -- l conflict
        let A:=scalePolDiff F l d p; have he : screen F d A=0:= by
           change beam d _=_; rw [scalePol_physical]; change beam d (scaledPol M l x)=0;rw [← M.basis.sum_repr x,map_sum,map_sum]; -- x defeq
           have ht: ∑ i:I,f i • level (vapor G) r (b i)=0:= by
              let P:= (level (vapor G) r) ∘ₗ (alpha S d); have ht:P x=0:= by rw [show P x=level (vapor G) r (alpha S d x) from rfl,hp,map_zero] -- rw?
              change ∑ i:I,M.basis.repr x i • P (M.basis i) =0; simp_rw [← map_smul,← map_sum]; exact (congr_arg P (M.basis.sum_repr x)).trans ht
           rw [← ht]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul,map_smul,scalePol_pure F _ _ ((F.level d).pure j), map_smul]; rcases lt_trichotomy r (race j) with h|h|h
           · have hj : level (vapor G) r (b j)=0:= Strong.none (hoist S j) h
             have hy : l (M.grades j)=0:= if_neg h.ne'; rw [hy,hj];simp
           · rw [h, show l (M.grades j)=1 from if_pos h.symm, alpha_name S j,one_smul] -- rw inside L? h dependent let? 
           change f j • _= f j • _; rw [IH _ h j rfl];simp
        have hh : A=0:= screen_in F d (he.trans (map_zero _).symm)
        have hz:= congr_arg (fun p:Pert.Position.E F d=> M.coords (physicalLabel F d p) i) hh
        rw [show physicalLabel F d A= _ from scalePol_physical F l p, scalePol_eq F l x i, show l _=1 from if_pos hr.symm,one_mul,map_zero,map_zero] at hz; exact hz
   apply (physical_inj (F:=F)); rw [map_zero]; apply M.coords.injective; rw [map_zero]; exact funext (fun i=> hc (race i) i rfl)

lemma purchased (d:ℕ):LinearMap.range (coreP S d)=physicalJet G d:= by
   haveI : FiniteDimensional ℂ ↥(physicalJet G d):= by rw [← screen_range F]; infer_instance
   refine Submodule.eq_of_le_of_finrank_le ?_ ?_; · rintro _ ⟨z,rfl⟩; exact alpha_c S (physicalLabel F d z)
   rw [← screen_range F d]; exact ((LinearEquiv.ofInjective (screen F d) (screen_in F d)).symm.trans (LinearEquiv.ofInjective (coreP S d) (core_in S))).finrank_eq.le
end YM.PositionX.Bare
