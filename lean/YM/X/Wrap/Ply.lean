import YM.X.Wrap.Quiet
/-! # maximal decay from all three vertex legs. Supplies arbitrary exterior marks in census Aw. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Crate
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics Reed Braid
open Clove Crystal Gravity Shelf Haze Ocean Interval Size Fielding Print PertExtension LatticePT Plate
open Finset LiftMark Tensor
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {V I T:Type*} {i k d:ℕ} {G:Gauge}
namespace Condition
variable (B:Submodule ℂ (T→ℂ))(S:Finset I)(Q:T→Symmetric V)(u:I→Set (Stella V T))
abbrev extractP : Code V T→ₗ[ℂ] (T→ℂ):= LinearMap.pi (fun i=> (MvPolynomial.aeval (0:V→ℂ)).toLinearMap ∘ₗ LinearMap.proj i)
def slew (l:List (Stella V T)): Module.End ℂ (Code V T):= match l with
   | []=> LinearMap.id
   | x::l=> slew l ∘ₗ stream Q x
lemma course (l:List (Stella V T))(p:Code V T): slew Q l p=swarm Q l p:= by induction l generalizing p with| nil=> change p=_;rw [swarm]| cons x l IH=> rw [slew,LinearMap.comp_apply,IH,swarm]
def school : Submodule ℂ (Code V T):= ⨅ (l:List (Stella V T)) (_: ∀ a∈l,∃ i∈S,a∈u i), Submodule.comap (extractP ∘ₗ (slew Q l)) B
lemma schools (p:Code V T): p∈ school B S Q u↔Condition B Q S u p:= by simp_rw [school,Submodule.mem_iInf,Submodule.mem_comap,LinearMap.comp_apply,course];rfl
variable {B S Q u}
lemma apiece (a:Stella V T) : fleet (piece a)=0:= by ext1 z; exact aeval_glyph (a z)
lemma fconst(f:T→ℂ):fleet (V:=V) (charge f)=f:= by ext1 z; exact MvPolynomial.aeval_C ..
lemma fzero : fleet (0:Code V T)=0:= map_zero (extractP (V:=V) (T:=T))
lemma fmul (p q:Code V T): fleet (p*q)=fleet p*fleet q:= by ext1 z; exact map_mul (MvPolynomial.aeval (0:V→ℂ)) (p z) (q z)
lemma fadd (p q:Code V T): fleet (p+q)=fleet p+fleet q:= map_add extractP p q
lemma fcoin (x a:Stella V T): stream Q x (piece a)=charge (cross Q x a):= by ext1 z; exact Braid.link (Q z) (x z) (a z)
lemma notion {f:T→ℂ}(h:f∈B): Condition B Q S u (charge f):= by
   intro l _; simp_rw [← course]; rcases l with _|⟨x,l⟩; · unfold slew; rw [LinearMap.id_apply,fconst]; exact h
   rw [slew,LinearMap.comp_apply,show stream Q x (charge f)=0 from funext (fun i=> by rw [stream_point]; exact Derivation.map_algebraMap ..),map_zero,fzero]; exact B.zero_mem -- fleet0 not rfl
lemma leaves (a:Stella V T)(h:∀ i∈S,∀ v∈u i, cross Q v a∈ B): Condition B Q S u (piece a) := by
   intro l hl; rcases l with _|⟨x,l⟩; · rw [swarm,apiece]; exact B.zero_mem
   obtain ⟨i,hi,hv⟩:= hl x (by simp); rw [swarm,fcoin]; exact notion (h i hi x hv) l (fun y he=> hl y (List.mem_cons_of_mem x he))
variable {C' D:Submodule ℂ (T→ℂ)}{p q : Code V T}
lemma campus (hp:∀ a:T→ℂ,a∈C'→∀ b:T→ℂ,b∈D→ a*b∈B)(h:Condition C' Q S u p)(ht:Condition D Q S u q): Condition B Q S u (p*q):= by
    intro l; induction l generalizing p q with
    | nil=> intro _; rw [swarm,fmul]; exact hp _ (sp_free _ _ _ _ _ h) _ (sp_free _ _ _ _ _ ht)
    | cons x l IH=>
       intro hl; obtain ⟨i,hi,hx⟩:= hl x (by simp); let L:=stream Q x; let t₁:= q*L p; let t:= (fun (x:V) (y:V)=> x); have he(v:Stella V T)(h:v∈l):∃ i∈S,v∈u i:= hl v (List.mem_cons_of_mem x h)
       rw [swarm,show stream Q x (p*q)=p*(L q)+ (L p)*q from ?_,← course,map_add,course,course,fadd]; exact B.add_mem (IH h (stepW _ _ _ _ _ ht x hi hx) he) (IH (stepW _ _ _ _ _ h x hi hx) ht he)
       funext z; simp only [L, stream_point, Pi.mul_apply,Pi.add_apply,Derivation.leibniz,smul_eq_mul]; ac_rfl
end Condition
end YM.PositionX.Crate
