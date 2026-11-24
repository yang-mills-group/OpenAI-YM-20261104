import YM.SignedWilsonExpansion.Kane.Matte
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.SignedWilsonExpansion.Kane
open Function Filter Set Table Spec Climb Trace Trace.Pilot PhysMS PhysMS.Frame
open Extraction Order Spin Next.UVStress OPE OPE.Orbits Levy
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 Dframe FVA2.Scale.Level Future
open Belfry Belle Dancer Belfry.Crisis Belfry.Classroom Belfry.ScaleFits Commission
open scoped BigOperators Topology ContDiff Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(W:ℝ→tower S)(L:Leading F W)
variable {b d e j n:ℕ}{ι:Type}{l:Filter ι}{g r ε:ι→ℝ}
namespace Tilted
open Asymptotics Dancer.Shell Commission.Gram SeatsW
-- admissible ratio step from mixed certificate.
structure Witness (d:ℕ)(l:Filter ι)(r g:ι→ℝ): Prop where
   mirror : ∃ (a:Axis)(x:ι→Points 2),Tendsto x l (𝓝 ( Gram.nodes a )) ∧ ∀ u w: Sec G d,Tendsto (MergeGeometry (F:=F) (W:=W) (r:=r) (g:=g) u w x) l (𝓝 (Paar ( GramW G d a ) u w))
variable {F W}
-- finances ∀r small.Global issue all pairs.Actor. no b=0 branch.Lo.Se.Y.
abbrev handheld (W:ℝ→tower S) (F:Final C f S)(d:ℕ)(l:Filter ι) : Prop := ∀ r:ι→ℝ,Tendsto r l trail→∀ g:ι→ℝ,( ∀ᶠ i in l, g i∈Set.Icc (-(Real.log 2)) (0:ℝ) ) → Tilted.Witness F W d l r g
lemma sprout (A:ℝ) (u:0≤A)(p:∀ᶠ i in l, g i∈Icc (-A) 0) : ∀ᶠ i in l, |g i| ≤ A:= p.mono (fun i hi=> abs_le.mpr ⟨ hi.1,hi.2.trans u ⟩)
lemma jumped (ε g:ι→ℝ) : jump (jump r g) ε=jump r (g+ε):= funext fun i=>by simp only [jump, Pi.add_apply,neg_add,Real.exp_add,mul_assoc]
lemma groundJump : jump r 0=r:=by ext i; simp [jump]
include L
variable (R:handheld W F d l)
include R
lemma microLocked (t:Tendsto r l trail)(u:∀ᶠ i in l,g i∈Icc (-Real.log 2) 0): Locked W r g l d:=by obtain ⟨x,y,p,v⟩:= ( R r t g u ).mirror; exact testimony L ( by_abs ( sprout _ ( Real.log_pos one_lt_two ).le u ) ) t d x y p v
lemma doubled (k:ℕ)(t:Tendsto r l trail)(u:∀ᶠ i in l,g i∈Icc (-(Real.log 2*2^k)) 0): Locked W r g l d:=by
    induction k generalizing r g with
    | zero=> simp only [pow_zero,mul_one] at u; exact microLocked L R t u
    | succ k ih=>
        let G'(i):= g i/2; let A:=Real.log 2*2^k; have hm : ∀ᶠ i in l,G' i ∈ Icc (-A) 0:= u.mono fun i p=> by
           obtain ⟨v,h⟩:=p; rw [pow_succ,←mul_assoc] at v; exact ⟨ by dsimp only [G',A]; linarith, div_nonpos_of_nonpos_of_nonneg h zero_le_two ⟩
        have p:FO l G':= by_abs ( sprout A (mul_nonneg ( Real.log_pos one_lt_two ).le (pow_nonneg zero_le_two _)) hm ); have hr: G'+G'=g:= funext fun i=> add_halves (g i); exact hr ▸ until_K d p p ( ih t hm ) ( ih ( recede p t ) hm ) -- hr ↔ check
lemma stable (t:Tendsto r l trail)(p:∀ᶠ i in l,|g i|≤Real.log 2 * 2^n): Locked W r g l d:=by
     let g₁(i):= min (g i) 0; let g₂(i):=max (g i) 0; let A:= Real.log 2 * 2^n; have h: ∀ᶠ i in l, g₁ i∈ Icc (-A) 0 ∧ -g₂ i∈Icc (-A) 0:=by
       filter_upwards [p] with i hp; rw [abs_le] at hp; have hz: 0≤ A:=mul_nonneg ( Real.log_pos one_lt_two ).le (pow_nonneg zero_le_two _); exact ⟨ ⟨ le_min hp.1 (neg_nonpos.mpr hz), min_le_right .. ⟩, ⟨neg_le_neg (max_le hp.2 hz),neg_nonpos.mpr ( le_max_right .. )⟩ ⟩
     have z:0≤A:=mul_nonneg ( Real.log_pos one_lt_two ).le (pow_nonneg zero_le_two _); let D:= jump r g₁; let C':=jump D g₂; have h1:=by_abs (sprout A z (h.mono fun i h=>h.1)); have h2:= by_abs ( sprout A (g:=-g₂) z (h.mono fun i h=> h.2)); have s2 : FO l g₂:= by simpa using! h2.neg_left
     have v:= doubled L R n (r:=C') ( recede s2 (recede h1 t) ) (g:=-g₂) ( h.mono fun i h=> h.2); have he:= clockRise h2 d v; rw [ show jump C' (-g₂)=D from (jumped ..).trans ( by rw[add_neg_cancel,groundJump]),neg_neg ] at he; have hv:=until_K d h1 s2 ( doubled L R n t (h.mono fun i h=>h.1) ) (show Locked W D g₂ l d from he); rwa [ show g₁+g₂=g from funext (fun i=> (min_add_max (g i) 0).trans (add_zero _)) ] at hv
lemma hostages (t:Tendsto r l trail)(p:FO l g) : Locked W r g l d:=by
     obtain ⟨A,hp⟩:= isBigO_iff.mp p; obtain ⟨k,hK⟩:= (((tendsto_pow_atTop_atTop_of_one_lt (show 1<(2:ℝ) from one_lt_two)).const_mul_atTop (Real.log_pos (by norm_num: 1<(2:ℝ)))).eventually_ge_atTop A).exists
     exact stable L R (n:=k) t (hp.mono fun i p=> (show |g i| ≤ A from by simpa using p).trans hK)
omit R
lemma adZ (T:FieldEnd G 0)(v:adm T): T=1:=by
    obtain ⟨p,rfl⟩:=v; have he : p.val ( Normalize.leaf G 0 )=0:= p.property.1; ext1 v; rw [stood]; rw [show p.val v=0 from Veto.pass0 p.val he v]; rw [add_zero]; rfl
lemma atZero (t:Tendsto r l trail)(p:FO l g) : Locked W r g l 0:=by
    have h: (fun i=>bend W (r i) (jump r g i) 0- Dial 0 (g i))=ᶠ[l] (fun _=> (0:FieldEnd G 0)):=by filter_upwards [ adm_bend L t ( recede p t ) 0 ] with i p; rw [ adZ L _ p,adZ L _ (adm.Dial _ 0) , sub_self (1:FieldEnd G 0) ]
    refine SeatsW.sameSalary (shine.mpr (constant (0:FieldEnd G 0))) h.symm (.refl ..)
lemma Patch_neighbor (t:Tendsto r l trail)(p:FO l g)(v:∀ d,0<d → handheld W F d l) : Neighbors l (Seats W r (F:=F) (fun _=>none)) (Seats W (jump r g) (F:=F) (fun _=>none)) g (fun i d=> bend W (r i) ( jump r g i ) d):=by
     refine ⟨ p, fun d=> PatchLocked L p t (?_),fun d n=>?_ ⟩
     · rcases Nat.eq_zero_or_pos d with h|h; · subst d; exact atZero L t p
       exact hostages L (v d h) t p
     apply Eventually.of_forall; intro i x _; ext1 u
     change S.classMoment S (fun _:Fin n=>d) (jump r g i•x) (fun j=> walk W (jump r g i) d (u j))= S.classMoment S (fun _:Fin n=>d) (r i• ellipse ( g i ) x) (fun j=> walk W (r i) d ( bend W (r i) (jump r g i) d (u j))); simp_rw [swing]; rw [ellipse,jump,mul_smul];
end Tilted
end YM.SignedWilsonExpansion.Kane
