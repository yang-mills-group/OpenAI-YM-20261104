import YM.FVA2.O.Pad.Vest
import YM.FVA2.O.Tune.Winner
/-!
# Complete a local generator to a response of the MS evolution

For obtaining exact terms to subtract at a given rank (`generatorZ`, `FlowZ`).
Use auxiliary unphysical markers for this construction, and the MS existence
results **with** their rank, cost hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Pad
open MS Function Filter Set Finset MS.Plane MeasureTheory Real Metric
open Momentum Heat Koszul Flux High Landau Detect MS.Color Book Signal Arts Alps MS.Local.Physical
open Wire Spin Pilot Emit Halo Convolve MS.City MS.Rake Latch Job LogTime IntervalFamily Dock MS.Land Lives Tune Outlook
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge}{m k n:ℕ}{t b:ℤ}{F:Law G}{B:Deck G}{K:Booked B}{M:MS_Data G K}{P:IntervalFamily I}{η:I→ℝ}{X:T ( Glade G I )}
lemma return_x (F:Law G): bracket F 0=F:= by
    funext l; induction l generalizing F with
    | nil=>exact one_mul _
    | cons i l ih=>
      rw [D_eval _ (bracket F 0), from_head,Pi.smul_apply, ih, show accept i.1=1 from ?h,one_smul,show shrink i.1=i.1 from ?hMM ] ; · rfl
      case h=> rcases i with ⟨⟨⟨_|i,_⟩,_⟩,k⟩ <;> first | rfl|exact if_pos i.isLt
      case hMM=> rcases i with ⟨⟨⟨_|i,b⟩,j⟩,k⟩ <;> first| rfl | simp [shrink,down,i.isLt]
lemma blank (n:ℕ)(b:ℤ): Badge false (fun _ : ℂ=> (0:Mob G)) n b:= Halo.Pace.prepay (t:=b) (r:=n) ( fun _=> (Halo.Pace.zero  ) ) Rock.Sturdy0 (fun _ _=> map_zero _ ) -- arg
lemma gift (M: MS_Data G K)(hp:F∈ Local.Physical.Lease G (n:ℤ) k b): ∃ Y Q, comet n b M.bulk ( gloss ( fun i=> if i=0 then bracket F else 0 ) ) Y Q:= by
    refine satisfyY M.bulkOK fun i=> ?_; unfold gloss; dsimp only; split_ifs; exact badgeV F n k hp; exact blank _ _
lemma yarn (hp:F∈ Local.Physical.Lease G (n:ℤ) k b)(Y:Blue G)(Q:CostsM G)(hu:comet n b M.bulk ( gloss (fun i=> if i=0 then bracket F else 0) ) Y Q) : Diversity (letIn n η Y 0 - fun (_:I) (_:ℝ)=> F) ((k:ℤ)-2) := by
    intro i s; obtain hv:= HM hu (s:=s) (y:=η i) (by simpa [gloss] using! badgeV F n k hp) (r:=(k:ℤ)) (by rw [if_pos (by rfl)]; exact fun i=> (Pad.pick (m:=i) (initial_p F n k hp)).up ); simpa only [ ite_true,Pi.sub_apply,return_x ] using! hv 0
abbrev Reps (X:T ( Glade G I ))(d:ℤ)(P: IntervalFamily I) := ∀ n:ℕ,Latch.Lease false false P.primary ( sweep P ( X n ) ) (fun i=> P.primary.length i ^ (-d))
lemma repreprice {p q:CostsM G}{Y:Blue G}(h:allowance P η)(hp:comet n b M.bulk p Y q): Reps (letIn n η Y) n P:= fun i=> beacon (Host.host (gang (hp i))) h
lemma degreeI (X:T ( Glade G I ))(H:Law G)(k:ℕ)(h:Ranked false k H)(hx:Diversity (X 0-fun _ _=> H) ((k:ℤ)-2))(i:I)(s:ℝ): Book.mask k ( X 0 i s )=H := by
    funext l; by_cases hr:l.length=k; · rw [ Book.enough _ (by exact_mod_cast hr) ]; exact sub_eq_zero.mp (hx i s l (by omega) )
    rw [Book.strange _ (by omega),h _ (fun i=>Bool.noConfusion i) hr]
-- rank lead includes prior cap.Horizon every
structure FlowZ (F:Glade G I)(k:ℕ)(H:Law G): Prop where
    reach: Diversity F k
    tops i t l (h:l.length=k): F i t l= H l
lemma floorZ (hr: Ranked false k F)(h:Diversity ( X 0-fun _ _=> F ) ((k:ℤ)-2)): FlowZ (X 0) k F := by
    constructor; · have ht:Diversity (fun (_:I) (_:ℝ)=>F) k:= fun _ _ l hl=>hr _ (fun v=>Bool.noConfusion v) (by omega); simpa only [sub_add_cancel] using uh (behind h (by omega)) ht
    intro i t l hz; exact sub_eq_zero.mp (h i t l (by omega))
lemma τzero : nav M η X 0= ( both G I ).J ( X 0 ):= by change _+ pairW (both G I).C (Lives.gather M η) X 0=_; rw [paired, Finset.Nat.antidiagonal_zero,Finset.sum_singleton, show Lives.gather M η ((0,0):ℕ×ℕ).1=0 from zero_B M,map_zero,LinearMap.zero_apply,add_zero,promised]
lemma ward_z (hx: Response X M η t)(ht:Diversity ( X 0 -fun _ _=> F ) ((k:ℤ)-2))(hr:Ranked false k F): FlowZ ( nav M η X 0 ) k ( natQ F ):= by
    have hv:=( floorZ hr ht ).reach; obtain he:= cdrop ( hx.life 0 |>.cross ) hv realityB; have h:Diversity ( Lives.Z G I ( X 0 - fun _ _=> F )) ((k:ℤ)-2):= fun i t=> Wind.Modeled.Qmax _ (ht i t); rw [ map_sub ] at h; have hp:= uh h he; rw [ sub_add_eq_add_sub ] at hp; rw [← LinearMap.add_apply,← front G I,← τzero ( M:=M) (η:=η)] at hp; exact floorZ (rankQ hr) hp 
lemma generatorZ (M: MS_Data G K) (hp:F∈ Local.Physical.Lease G (n:ℤ) k b)(h:allowance P η): ∃ X:T ( Glade G I ),Response X M η b ∧ Reps X n P ∧ FlowZ ( nav M η X 0 ) k ( natQ F ):= by
    obtain ⟨Y,Q,hY⟩:=gift M hp; obtain hx:= Response.mark (η:=η) hY; exact ⟨ letIn n η Y,hx,repreprice h hY, ward_z hx (yarn hp Y Q hY) ( lease_one.mp hp ).2.2 ⟩
end YM.FVA2.O.Pad
