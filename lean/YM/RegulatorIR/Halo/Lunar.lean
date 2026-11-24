import YM.RegulatorIR.Halo.Metric

/-!
Fixed-length seed cutoffs; constants do NOT compare across original runs.
Prove uniform defect localization over replicas rooted (at their canonical
singular sets). Later ordinary Ward limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo.Aug
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim Finset PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Sight Uniform
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge} {W:Type}{M:W→ℕ}{n:Page M→Side}
variable {S: Heir n G} (H:Reel S) (Z:S.Accounts)
variable {L:Meter W}{p a i e r:ℕ}
def glaze (a:ℕ) := a+6+(a+6)
variable (T : Amenities S L p (glaze a))(B: S.Supplies Z L p (glaze a))
variable (V:H.Follows Z) (hp: Common H)
local notation "E" => eternal H
local notation "U" => grove H
variable (w:W)
local notation "P" => tele H Z w

def gap (j:ℕ)(h:j ≤ M w)(e r:ℕ)(i:Side):= ((P).change (sheet w j h i) e r)
include T B V hp
lemma horizons (j:ℕ)(he:j ≤ M w) :∀ e,e ≤ p→∀ r,0<r→ Claim light ((lpost H w j he).pear a) 1 (gap H Z w j he e r):=by
 induction j with
 | zero =>
    intro e _ r hr
    have h (z:Side) : gap H Z w 0 he e r z=0:=by
       change Deck.deckSum (radar H w (sheet _ 0 he z)) _-Deck.deckSum _ _=0
       exact sub_self _
    simp_rw [funext h];exact Claim.zeroQ (r:=r)
 | succ j ih=>
    intro e hq r hr
    let F:= known H w j he;let A:= (fun _:Side=>delay (S:=S) w j he); let hv(z:Side):0<A z:= (E w).hl ((stepf w j he z).next)
    let U0:= F.incoming A hv; let K:=F.insideRoom A hv;let X:= F.outgoing A hv;let Hp:= U w hp
    let C:= fun z:Side=>(stepf w j he z).prev
    let g:=fun z =>(P).bulk (C z);let h':=fun z=>(P).orb (C z)
    have hm:∀ e,e ≤ p→∀ r,0<r→ Claim light (U0.pear a) 1 (U0.vgap (fun w=>g w e r) (fun w=>h' w e r)):=by
       intro i hg k hr
       let D:= lpost H w j (Nat.le_of_succ_le he)
       have ht: Claim light (D.pear a) 1 (U0.vgap (fun w=>g w i k) (fun w=>h' w i k)):= ih _ i hg k hr
       apply Post.fewer hv (M:=D) _ ht
       intro z; exact (E w).climb (stepf w j he z)
    have hd: Beam light (K.cone a) F.forecast:= K.descent (spurs H w T j he) (by unfold glaze; omega)
    have he' (z:Side): Layer.Sym (F.room z) (F.room z) (F.forecast z):= suitable Hp (stepf w j he z)
    let T':= U0.vgap (fun w=>g w e r) (fun w=>h' w e r)
    have HH: Claim light (X.pear a) 1 (F.kick T') := F.out_bill (Claim.draft_budget (F.orb_bill (hm e hq r hr)) (K.wrap_beam hd he'))
    letI : ∀ z:Side,Fintype (Book G (big w n ((stepf w j he z).prev))):= fun _=>inferInstance
    letI :∀ z:Side,Fintype (Book G (big w n ((stepf w j he z).next))):= fun _=>inferInstance
    have hx:= F.assembly g h' (e:=e) (r:=r) (b:=6) (u:=a) (beams H w T j he) (fete H w j he) (fun z=>hort Hp (stepf w j he z)) (fun z i j' _=>natural_o Hp (stepf w j he z) i j') (fun z i j _=>helium Hp P (knows H Z w hp V) (C z) i j) (fun z=>essential Hp (stepf w j he z)) (fun z=>(P).cap_b (fun i=>essential Hp i) _) (fun z=>(P).cap_o (fun i=>essential Hp i) _) (fun i k j'=>conflict H w Z B j he (k.trans hq)) (fun i k j'=> added H w T j he (k.trans hq)) (fun i k v hi=>hm i (by unfold Earlier at v;omega) k hi) hd he' hr
    have hb : Claim light (X.pear a) 1 (fun w=> (X.vgap (fun z=>(F.grid z).pure (g z) e r) (fun z=>(F.grid z).common (h' z) e r) w - F.kick T' w)+F.kick T' w):= Claim.add hx HH
    change Claim light (X.pear a) 1 _; convert hb using 1; ext1 z
    let p':=stepf w j he z;change (P).change p'.next _ _= X.vgap _ _ z - F.kick T' z + F.kick T' z
    rw [sub_add_cancel, Accounts.change,← (P).step_o p',← (P).step_v p'];rfl
end YM.RegulatorIR.Halo.Aug
