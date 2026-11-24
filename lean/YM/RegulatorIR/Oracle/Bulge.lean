import YM.RegulatorIR.Oracle.Beacon

/-! Resolve inverse on slice. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field Bark
open FreeResolvent (Slot PAC Vec component ix tensor)
open Exterior RG Wilson Matrix Halo Profiles Push Precision
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {G: Gauge} {n p:Side} {X Y A V: Type}
-- ledger uniqueness e=$c$. Algebra Pad $C$. 
lemma inwardQ [Fintype X][DecidableEq X]{A B M D:Matrix X X ℝ} (h:M*M=M)(hx:D=M*A*M+(1-M))(hv:D*B=1)(_hd:B*D=1): M*(A*(M*B*M))= M ∧ M*(M*B*M)=M*B*M :=by
 have hh : M*(A*(M*B*M))=M*(D*B)*M:=by
    rw [←mul_assoc M D B,hx,mul_add,mul_sub,h,mul_one,sub_self,add_zero,←mul_assoc M,←mul_assoc M,←mul_assoc M M A,h]; simp only [mul_assoc]
 refine ⟨by rw [hh,hv,mul_one,h],?_⟩
 rw [←mul_assoc,←mul_assoc,h]

variable (P:Patch)(K:KernelChoices)(G:Gauge)(B:Precision.Bed)
variable {σ Ω α:ℝ} {S:Clip}
variable (F: Hall B σ Ω α S) (Z:P.Branches K G)

-- complement-mask product now only in Wind: structured projection repeated.
def hearth := lap (lap (pension P G) (cable P K G B F Z)) (pension P G)
lemma powersV : chestE (blockQ G P.L) (blockQ G P.L) (widthK P K G σ Ω α) (hearth P K G B F Z) (markup P K G σ Ω α):=by
 have ht:=(effects P K G B F Z).choose_spec.2.1
 have hh:=(width_pos P K G B F).le
 have he:= ((pensionE P G).lapB ht hh).lapB (pensionE P G) hh
 simpa only [one_mul,mul_one] using! he
lemma heatP : Billed (hearth P K G B F Z):=(powersV P K G B F Z).billed (width_pos P K G B F).le (billingC _ _ _ _ _ _)
lemma phaseT : Albedo (blockQ G P.L) (blockQ G P.L) (hearth P K G B F Z):= ((promised P K G).lap (effects P K G B F Z).choose_spec.1).lap (promised P K G)
lemma crown : let Q:= hearth P K G B F Z; let C:=pension P G
               lap C (lap (stableK P K G B) Q)=C∧lap C Q=Q:=by
 intro Q C
 let X:= blockQ G P.L; have hf:= heatP P K G B F Z;have he:= phaseT P K G B F Z;have ht:= promised P K G; --fix
 have hp (n:Side): ledgerRow X X (lap C (lap (stableK P K G B) Q)) n=ledgerRow X X C n ∧ ledgerRow X X (lap C Q) n=ledgerRow X X Q n:=by
    have hS:= savings P G; have hu:= lifetimeK P K G B F
    obtain ⟨hx,h₁⟩:= ortho_cable P K G B F Z n
    rw [Ledger.lap X X X n hS (hu.lap hf) ((pilotK P K G B).lap he), Ledger.lap X X X n hu hf he,Ledger.lap X X X n hS hf he]; unfold Q hearth C
    have hy:=cafe P K G B F Z; rw [Ledger.lap X X X n (hS.lap hy) hS ht,Ledger.lap X X X n hS hy (effects P K G B F Z).choose_spec.1]
    refine inwardQ ?_ ?_ hx h₁
    · rw [physicalP P K G]; exact FreeResolvent.Shell.on_on _
    rw [touches P K G B F,physicalP P K G,physicalK P K G B F];rfl
 have hq:= savings P G; have h:= lifetimeK P K G B F
 exact ⟨solely _ _ (hq.lap (h.lap hf)) hq (ht.lap ((pilotK P K G B).lap he)) ht (Eventually.of_forall (fun _=> hp _ |>.1)),solely _ _ (hq.lap hf) hf (ht.lap he) he (Eventually.of_forall (fun _=>hp _|>.2))⟩
include F
lemma symmetryQ: Function.swap (cousin P K G B)=cousin P K G B :=by
 -- use finite ledger uniqueness. Need transpose Billed via two-way via cargo strip transpose. from unwr
 let Q:=cousin P K G B; let X:=blockQ G P.L; let a:=spliceR P K G B
 have hx: FundE X X σ Q:=by
    have hp:= fond X X _ (cargoW X X (shellsC P K G B F) (show trunkCost P K G σ Ω≠⊤ by unfold trunkCost;finiteness)); rw [unwind X X a] at hp;exact hp
 apply solely _ _ (hx.buys F.pos.le).2 (hx.buys F.pos.le).1 a.swap a (Eventually.of_forall (fun i=>?_))
 intro f; rw [Ledger.rev _ _ _ a];
 have he:= lifetimeK P K G B F;have hh:= touches P K G B F f; let M:=stableK P K G B;let L':=OrthoQ P K G
 rw [show ledgerRow (blockQ G P.L) _ Q f= FreeResolvent.Shell.pad _ _ from hh,← physicalK P K G B F]; unfold FreeResolvent.Shell.pad FreeResolvent.Shell.slice
 rw [Matrix.transpose_add,Matrix.transpose_mul,Matrix.transpose_mul, ← Ledger.rev X X f (pilotK P K G B), FreeResolvent.Shell.clockwise,FreeResolvent.Shell.undo, show Function.swap M= M from ?_];rw [Matrix.mul_assoc]
 apply funext;intro i;apply funext;intro j;change crust G B j i+ _=crust G B i j+ _; rw [show crust _ B j i=_ from congr_fun (congr_fun (symmetry_h G B F.floorP F.pos.le F.paid F.stripP.2.1) i) j]; apply congr_arg;apply congr_arg (fun z:ℝ=>K.penalty*z); exact tsum_congr (fun _=> mul_comm ..)
lemma t_warm : Function.swap (hearth P K G B F Z)=hearth P K G B F Z:=by
 let X:=blockQ G P.L;let W:= cable P K G B F Z;let C:=pension P G
 have he:= phaseT P K G B F Z
 have hV: FundE X X (widthK P K G σ Ω α) (hearth P K G B F Z) := by
    have hv := fond X X _ (cargoW X X (powersV P K G B F Z) (billingC _ _ _ _ _ _)); rw [unwind X X he] at hv;exact hv
 have hv:= cafe P K G B F Z; have hx:= savings P G;have hm:= promised P K G
 apply solely X X (hV.buys (width_pos P K G B F).le).2 (heatP P K G B F Z) he.swap he (Eventually.of_forall (fun i=>?_))
 intro f; rw [Ledger.rev _ _ _ he,hearth,Ledger.lap X X X f (hx.lap hv) hx hm,Ledger.lap X X X f hx hv (effects P K G B F Z).choose_spec.1]
 let w:= ledgerRow X X W f;let c:=ledgerRow X X C f;let q:=ledgerRow X X (cousin P K G B) f
 obtain ⟨a,b⟩:= ortho_cable P K G B F Z f
 have hp:w.transpose=w:=by
    have hy:q.transpose=q:=by unfold q;rw [← Ledger.rev X X f (spliceR P K G B),symmetryQ P K G B F] -- arg Z if no
    have he : w.transpose*q=1:=by rw [← hy, ← Matrix.transpose_mul,show q*w=1 from a,Matrix.transpose_one]
    calc
      _ = w.transpose*(q*w):= (by rw [show q*w=1 from a,mul_one])
      _ = _ := by rw [← mul_assoc, he,one_mul]
 change (c*w*c).transpose=_;rw [Matrix.transpose_mul,Matrix.transpose_mul,show c.transpose=c from ?_,hp,← Matrix.mul_assoc]
 unfold c C;rw [physicalP P K G]; exact FreeResolvent.Shell.clockwise _
end YM.RegulatorIR.Oracle
