import YM.FVA2.Invoice
/-!
# Equality to PhysicalSum on the pure stencil inputs

Proof with unscaled and scaled stages. No QME assumptions on Master beyond what
was proved finite from action and inverted-root projection. Source includes any
finite list and rank rescaling applied to each mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Function Set Finset Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open MS.Orbit.LogReal MS.Bare MS.Cylinder MS.Cylinder.Taylor MS.Puff MS.Puff.Mom MS.Book
open MS.Book.Convolve MS.Book.Program MS.Puff.Engine MS.Swirl.Near MS.Cylinder.Lab MS.Native.Wilsonian MS.Puff.Actors MS.Fleet
open PertExtension PertExtension.Orb Substitute Matrix Coupling Ends Inserted
open scoped Classical Topology ContDiff
variable {G:Gauge} {n:Side} (φ:Team)(η:ℝ)(h:Even n.val)
local notation "A"=> Choice.allLetters G n
local notation "P"=> Words G n
local notation "I"=> FixedMode G n
local notation "F"=> rootedVertex G n
local notation "H"=> Letter.grain (baseProp G n) (baseFix G n)
local notation "M"=> Master G n true
local notation "X"=> Bplane G n
local notation "V"=> BackRoot (G:=G) (n:=n)
local notation "ψ"=> (χ G n)ᵀ * Fourier G n
local notation "p"=> Letter.p
local notation "π"=> σbranch (G:=G) (n:=n)
local notation "τ"=> shift φ η

lemma at_F (G:Gauge)(n:Side)(a : ℕ): landL (n:=n) (Native.Wilsonian.core G a) = pay true • ((full n).total (priorFull G n)) a:= by
   unfold landL; rw [map_smul]; exact congr_arg (pay true • ·) (congr_fun (read_total (G:=G) (n:=n)) a)
lemma p_ψ : TieField ψ p π := by
   rw [ index_L ]; intro i j he; rw [ ← label_compatible i ]; exact kind_F _ j he -- inspect
-- unweighted before shift.

def invoices (n:Side)(G:Gauge): SpecB (Words G n) := fun i=> if i=0 then 0 else landL (Native.Wilsonian.core G i)
local notation "Γ0"=> invoices n G

lemma fin_f : Γ Γ0 p:= by
   intro i _; unfold invoices; split; exact (FeeP _).zero_mem
   rw [at_F]; exact (FeeP _).smul_mem _ (total_limits (full n) (prior_full_prop G n) i (Set.mem_univ _))
variable {W:Type}[LinearOrder W] (x:W→ Cover)(s:Finset W)(z:W→ Unscaled G)

-- pure marks before shift
abbrev listPay : W→SpecB P:=fun i j=> landV (x i) (levels (z i).degree (z i).stencil j)
def pencil {D:Type} (F':W→SpecB D): Mate D W:= fun v=> if h:v.Nonempty then if v.card=1 then F' (v.min' h) else 0 else 0
local notation "P1"=> pencil (listPay (n:=n) x z)
local notation "T1"=> spars (fun i=> home n (x i) (z i))

lemma list_here {D:Type}(F': W→ SpecB D)(i: W): pencil F' {i}=F' i:= by simp [pencil]
lemma list_tb {D:Type}(F': W→ SpecB D)(s:Finset W)(h:s.card≠1): pencil F' s=0:= by unfold pencil; split <;> rfl
lemma prim_even (i:W) : EvenSeries p (listPay (n:=n) x z i) := (even_coeff _).mpr (fun j=> by change Pure _ _ (landV _ _); rw [Unscaled.levels_charge]; exact pure_mask (ink_p _ (glowGraph.never) _) _)
lemma prim_Γ (i:W): Γ (listPay (n:=n) x z i) p:= fun j _=> by
   unfold listPay; rw [Unscaled.levels_charge]; exact ⟨sym_mask (ink_s _ (glowGraph.never) ((z i).marks_grid _)) _, minH (Limit.mod _ _)⟩
lemma FontΓ : Γ (Font p P1 s) p:=by
   suffices hp:(Font p P1)∈ allIndex (allIndex (FeeP p) ℕ) (Finset W) from hp s (Set.mem_univ _)
   let S:= PermV (p:Sector P); have hv : Γ (S.unit) p:= refineπ useN (coin 1) feeUnit
   refine costCheer _ hv (fun _ hv _ he=>ΤΓ_pair hv he) ?_
   intro s _; by_cases h:s.card=1
   · obtain ⟨a,rfl⟩:=Finset.card_eq_one.mp h; rw [list_here]; exact prim_Γ x z a
   rw [list_tb _ _ h]; exact (allIndex _ ℕ).zero_mem
lemma homeΓ : Γ (Font p T1 s) p:= by
   rw [Font_invoice]; refine ((mark_insert _ (prior_root_prop G n) _ _ (invoice_germ s z x) (min_invoice s z x) ?_).finiteF);
   rw [actual]; have hv:=invoice_germ (n:=n) s z x; rw [actual] at hv; exact inert_from (root n) _ (original_inv s z x) hv
lemma exp_finF : promote ξ[ψ] (exp0 p Γ0)= exp0 π ( promote ξ[ψ] Γ0):= exp_change ψ p_ψ Γ0
include h
lemma root_weight : promote ξ[V] (exp0 p Γ0)= promote ξ[X] (exp0 p F):= by
   rw [exp_change _ pays_full, exp_change _ pays_plane]; apply congr_arg; funext i; unfold invoices rootedVertex;
   simp only [promised]; split_ifs with he; · simp
   exact land_charge h i
lemma Vac_identity : ℶV M (exp0 π ( promote ξ[ψ] Γ0))= ℶV H (exp0 p F):= by
   funext i; rw [← exp_finF]; change View M ( ξ[ψ] _ ) = View H (exp0 p F i);
   rw [view_root h, view_down h (exp0 p F i) (fee_spec (expΓ root_regular i (Set.mem_univ _))).2]; exact congr_arg _ (congr_fun (root_weight (G:=G) h) i)
   exact (fee_spec (expΓ fin_f i (Set.mem_univ _))).2
omit h
lemma signs_w : promote ξ[V] (Font p P1 s)= promote ξ[X] (Font p T1 s):= by
   rw [tether_marks _ pays_full, tether_marks _ pays_plane]; refine congr_fun (congr_arg _ ?_) s
   funext a; by_cases he:a.card=1
   · obtain ⟨b,rfl⟩:= Finset.card_eq_one.mp he; rw [Function.comp_apply,Function.comp_apply,list_here,sp_here]; funext j; exact (z b).levels_pull (x b) j
   simp_rw [Function.comp_apply,list_tb _ a he,sp_e _ a he,map_zero]

local notation "B"=> promote ξ[ψ]
local infixr:70 " ♫ "=> Actors.core (PermV p)
include h
lemma earnings : ℶV M ((PermV π).core (exp0 π (B Γ0)) (B (Font p P1 s)))= ℶV H ((exp0 p F) ♫ (Font p T1 s)):= by
   let T := promote ξ[X]; let U:= (Font p P1 s); let S:= (Font p T1 s)
   rw [← exp_finF];
   have hp:= ΤΓ_pair (expΓ root_regular) (homeΓ x s z (n:=n));
   have ht : B (exp0 p Γ0 ♫ U)=(PermV π).core (B (exp0 p Γ0)) (B U):= ((tether ψ p_ψ).Extrapolation useN).craft _ _
   change ℶV M ((PermV π).core (B (exp0 p Γ0)) (B U))=_; rw [← ht]; funext i;
   change View M (ξ[ψ] _) = View H ((exp0 p F ♫ S) i)
   rw [view_down h ((exp0 p F ♫ S) i) (fee_spec (hp i (Set.mem_univ _))).2,
       view_root h _ (fee_spec (ΤΓ_pair (expΓ fin_f) (FontΓ x s z (n:=n)) i (Set.mem_univ _))).2]
   have hv: promote ξ[V] (exp0 p Γ0 ♫ U) = T (exp0 p F ♫ S):= calc
       _ = (promote ξ[V] (exp0 p Γ0)) ♫ (promote ξ[V] U):= ((tether V pays_full).Extrapolation useN).craft _ _
       _ = T (exp0 p F ♫ S):= by rw [root_weight h, show promote ξ[V] U = T S from signs_w x s z]; exact (((tether X pays_plane).Extrapolation useN).craft _ _).symm
   exact congr_arg _ (congr_fun hv i)

lemma pure_cost : Endμ M π (B Γ0) ( B (Font p P1 s)) (pureVia n s (fun i=> z i.val) x) := by
   unfold Endμ; rw [earnings h,Vac_identity h]; exact (nakedC h s z x).2
omit h
-- coupling-program shift. Delete only i=0 not i.e. subtract *all* 2pt vertices.
lemma raw_rotate : substitute τ (B Γ0)= NRG (Stripped φ) η n G true := by
    funext i; by_cases hx:i=0
    · subst i; rw [τ_nil, Program.pay0]; change ξ[ψ] 0=0; rw [map_zero]
    rw [ NRG, if_neg hx ]; unfold style; rw [ strip_wobble ];
    simp_rw [rules,map_sum,map_smul]; refine Finset.sum_congr rfl fun j _=>?_
    by_cases ht:j=0
    · subst j; simp [cut,PowerSeries.coeff_one,hx]
    rw [promised, invoices, if_neg ht,land_bulk]

def undilute (z:Unscaled G) (φ:Team) : Actor G := fun u=> substitute (shift φ u) (levels z.degree z.stencil)
lemma install (x':Cover)(i:W): promote ξ[ψ] (listPay (fun i=>x'+x i) z i)= pointL ℕ (Mark_T G n x' (x i)) (levels (z i).degree (z i).stencil) := funext fun j=> (land_marks ..).symm
lemma snapped (u:Cover) : substitute τ ( B (Font p (pencil (listPay (n:=n) (fun i=>u+x i) z)) s)) =
      Font π (Marks (fun i=> undilute (z i) φ) η n u x) s:= by
    let K:=pencil (listPay (n:=n) (fun i=>u+x i) z)
    rw [ tether_marks ψ p_ψ]; change substitute τ (Font π ( B ∘ K ) s) = _
    have hv : Marks (fun i=> undilute (z i) φ) η n u x=substitute τ ∘ (B ∘ K):= by
       funext a; by_cases ha:a.card=1
       · obtain ⟨i,rfl⟩:=Finset.card_eq_one.mp ha; rw [mark_me, Function.comp_apply,Function.comp_apply, show K {i} = _ from list_here _ _, install ]; exact Program.comm (τ) _ (Mark_T G n u (x i))
       rw [mark_off ha]; simp_rw [Function.comp_apply, show K a=0 from list_tb _ _ ha, map_zero]
    rw [hv]; exact (functorG τ (share φ η) (actor π)).figure (Puff.SplitP.marked W) _ s
include h
theorem dressed_vertices_together (a:Cover): PhysicalSum G φ η n true s x a (fun i=> undilute (z i) φ)
     (substitute τ (pureVia n s (fun i=>z i.val) (fun w=>a+x w))) := by
    have hz : B Γ0 0=0:=map_zero (ξ[ψ])
    have hv:=γη τ (share φ η) π (show Matrix I I ℂ from M) hz (pure_cost h (fun w=>a+x w) s z); unfold PhysicalSum; rw [ raw_rotate,snapped ] at hv; exact hv
end YM.FVA2.Inversion
