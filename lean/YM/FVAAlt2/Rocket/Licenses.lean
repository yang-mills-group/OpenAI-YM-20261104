import YM.FVAAlt2.Rocket.Merits
import YM.FVAAlt2.Rocket.Campaign
/-!
# License. One Run, all thermal/UV numbers including the direct-top entry caps.

 Concrete scheduler: working uniformly inside each of a cofinal sequence of **thick
 admissible windows** of the Run. Window endpoints may depend on J stage; orbit terminal period is
 not the Run period. Measurement convention is exactly at actual spacing of fine R−ν⊕ points
 after $i$ reaches the corresponding J stage (native units). Algorithms & Bounds in
 the generic `Tour.final_stage` remain valid without the constant-plateau specialization if
 the RegulatorIR.Spectrum hypothesis and explicit extra physical scale budgets are met.
 This particular Schedule is a DIAGONAL subsequence of top/measuring/infrared spacings,
 explicit ages ($ℓ$ and $kN$). Keep same schedule for all q/orders; each **fixed order list** is
 licensed on an eventual tail. No claim of full actual-hierarchy continuation (nonperturbative)
 at arbitrary intervening distances, even if the base Run we extended has stronger results.
 In particular this allocation does not say the qcapt real->formal comparison error summit
 remains in its allowed regimes; they set their own tests. Not tuned to be Jewel (needs own
 additional purchases). Needed if carrying to those stronger full-phase claims.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lodge
open Function Set Filter MeasureTheory Topology Real Finset Lattice RG Precision Gauge
open Oracle Epoch Calibration Rocket Uniform Binding Diagram Ledger Taping Atlas
open PhysicalNext.Repeat.Legato Family Run
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X:Type} {G:Gauge}{K:KernelChoices} (Y:Oracle.Program K)(Z:∀ Q:Patch,Q.Branches K G)
-- next. capacity at fixed Q
abbrev through (p:ℕ):= max 14 (p+2)
abbrev cost (p j:ℕ) := Atlas.orders G Y p (through p) j (1/2) (by norm_num) (by norm_num) -- needs ?Z implicit
-- pre length. 
def anticipate (G:Gauge)(Y:Program K)(j:ℕ): ℕ:= (range (j+1)).sup fun p=> cost (G:=G) Y p j
-- post. Huge allowed gap. thickness Length. Peer Table. cover costs `lumber` exp^θ.
def pad (j:ℕ) (L:Side):ℕ:= ⌈ ((range (j+1)).sup (fun p=> Track.bills G Y j L.val Z p (through p))).toReal ⌉₊
def acquire (j:ℕ)(L:Side):ℕ:= pad Y Z j L+j+1
def shoulder (j:ℕ)(L:Side):ℕ:=2*(acquire Y Z j L* acquire Y Z j L)
lemma afford (j:ℕ)(L:Side) : _root_.LT.lt ((range (j+1)).sup (fun p=> Track.bills G Y j L.val Z p (through p))) ⊤:= Finset.sup_lt_iff (by norm_num)|>.2 (fun _ _=> (lt_of_le_of_ne le_top (Track.bills_f Y Z j L.val)))
lemma stamina (j:ℕ)(L:Side)(p:ℕ)(hp:p≤j): Track.bills G Y j L.val Z p (through p) ≤ ENNReal.ofReal ((acquire Y Z j L:ℕ):ℝ):=by
 set V:=(range (j+1)).sup (fun p=> Track.bills G Y j L.val Z p (through p)); have ht: V.toReal ≤ ((acquire Y Z j L:ℕ):ℝ) := le_trans (b:= (pad Y Z j L :ℝ)) (Nat.le_ceil _) (Nat.cast_le.mpr (by unfold acquire; omega)); exact le_trans (b:=V) (le_sup (f:=fun p=> Track.bills G Y j L.val Z p (through p)) (by simp [hp] : p∈range (j+1))) ((ENNReal.ofReal_toReal (afford ..|>.ne)).symm.trans_le (ENNReal.ofReal_le_ofReal ht))
variable (R:Run G)
local notation "T₀"=> R.family.path.levels
structure Contract (R:Run G)(Y:Oracle.Program K)(Z:∀ P:Patch,P.Branches K G): Prop where
   law : (R.family.path.levels).clock.kernel=K
   holds : PhysicalNext.Repeat.Legato.FVAAlt2.Windows R.family.path.levels (anticipate G Y) (shoulder Y Z)
theorem reception (G:Gauge)(hg:G.Simple){K:KernelChoices}(Y:Oracle.Program K)(Z:∀ P:Patch,P.Branches K G): ∃ R: Run G,Contract R Y Z:=by
 obtain ⟨R,hL,H⟩:= PhysicalNext.Repeat.Legato.FVAAlt2.buys hg Z (anticipate G Y) (shoulder Y Z); exact ⟨R,⟨hL,H⟩⟩
-- who starts the clock. minimum smoothing stage≥5 from any available calendar; D=degree
variable (T:Contract R Y Z)
namespace Contract
def floor:= max 5 T.holds.2.choose
-- issue paid center (depends only on stage j, not order; can use for any p afterward)
set_option quotPrecheck false
local notation "G₀"=> T.holds.2.choose
local notation:max "W_" i:max=> shoulder Y Z i ((T₀).clock.factor i)
section constants
local notation "J'"=> (T₀).clock.J
lemma gains(i:ℕ)(h:T.floor Y Z R ≤ i):∃ k, W_ i≤k ∧ ∀ j,k-W_ i≤j → j ≤ k+W_ i → J' j=i:= T.holds.2.choose_spec i (le_trans (le_max_right ..) h)
-- frame-level interpretation levels `ceil (earliest)`
def whereAt (i:ℕ)(h:T.floor Y Z R ≤ i):= (T.gains Y Z R i h).choose -- arg order 
variable (i:ℕ)(h:T.floor Y Z R ≤ i)
local notation "k"=>T.whereAt Y Z R i h
-- whole segment
lemma has_space : W_ i ≤ k := (T.gains Y Z R i h).choose_spec.1
lemma enrol {j:ℕ}(hn:k-W_ i ≤ j)(hp:j≤k + W_ i) : J' j=i:= (T.gains Y Z R i h).choose_spec.2 j hn hp
local notation "L₀"=> (T₀).clock.factor
lemma steady j (hn:k-W_ i ≤ j+1)(hp:j+1≤k + W_ i): R.family.S.block j = L₀ i := ( (T₀).fits.sameFactor j ).symm.trans (congrArg L₀ (T.enrol _ _ R i h hn hp))
end constants
local notation "L₀" => R.family.path.levels.clock.factor
variable (stamp:X→ℕ)(H:∀ x,T.floor Y Z R ≤  stamp x)
include H
lemma stone(x:X): 3≤ (L₀ (stamp x) ).val ∧ Odd (L₀ (stamp x) ).val:= by
    let j:= stamp x;let i:= T.whereAt Y Z R j (H x); have hk:0< W_ j:=by unfold shoulder; apply Nat.mul_pos (by norm_num) (Nat.mul_pos _ _) <;> unfold acquire <;> omega
    have hv: R.family.S.block i=L₀ (stamp x):= T.steady Y Z R _ (H x) i (Nat.le_trans (Nat.sub_le ..) (Nat.le_succ _)) (Nat.add_le_add_left hk _); rw [← hv]; exact ⟨(T₀).S.block_large i,(T₀).S.block_odd _⟩
def profile : Track X :={ J:= stamp,L:= L₀∘stamp, batch x:= acquire Y Z (stamp x) (L₀ (stamp x)), life:=fun x=>by unfold acquire; omega, stands:=fun x=> (T.stone Y Z R stamp H x).1,owns:=fun x=>(T.stone Y Z R stamp H x).2, issued:= fun x=> le_trans (le_max_left ..) (H x) }
local notation "V"=> T.profile Y Z R stamp H
lemma thick(x:X): (V).entire x= W_ (stamp x):= rfl
lemma batch_r {l:Filter X}(h:Tendsto stamp l atTop): Tendsto (V).batch l atTop:= tendsto_atTop_mono (f:=stamp) (fun x=> show _ ≤ pad Y Z (stamp x) (L₀ (stamp x))+stamp x+1 from by omega) h
lemma marks(p:ℕ)(hp:∀ w:X,p≤ stamp w): SatisfiesQ G Y (V).desk Z (V).ticketT p (through p) (1/2):=by
    let T':=V
    apply Track.field_p T' Y Z
    · intro x; have hu:= stamina Y Z (stamp x) ( L₀ (stamp x) ) p (hp x); exact hu.trans (ENNReal.ofReal_le_ofReal ((T'.hallL x).trans (T'.above x)))
    · exact le_max_right ..
    · exact le_trans (by norm_num: 3≤14) (le_max_left ..)
    exact fun w=> le_trans (le_sup (f:=fun p=> cost (G:=G) Y p (stamp w)) (by simp [hp w]: p∈ range (stamp w+1))) (T.holds.1 (stamp w))
-- use actual patch data in RegulatorIR. index clock launched at top on periodic branch
abbrev ceiling (x:X):= T.whereAt Y Z R (stamp x) (H x)
def atLevel (z:Page (T.profile Y Z R stamp H).entire):= T.ceiling Y Z R stamp H z.bindW-z.downW
lemma vert_j (v: Flap (T.profile Y Z R stamp H).entire): let j:= T.atLevel Y Z R stamp H v.next; T.atLevel Y Z R stamp H v.prev=j+1:=by
    intro j; let i:= stamp v.volW; have h:=T.has_space Y Z R i (H _); change T.ceiling Y Z R stamp H v.volW-v.offset=_; change (V).entire v.volW ≤ T.ceiling Y Z R stamp H v.volW at h; unfold j atLevel; dsimp only [Flap.next]; have hp:= v.ok; omega
lemma paid_level(v: Flap (T.profile Y Z R stamp H).entire)(N:ℕ): let S:=(V).desk; let op:= (R.family.path.levels.clock.op (T.atLevel Y Z R stamp H v.next) N); (S.rail K v).patch=op.patch ∧ ( S.rail K v ).kernel=op.kernel := by
    intro S op; set q:= T.atLevel Y Z R stamp H v.next; set f:= (T₀).clock; constructor; swap; exact T.law.symm
    let i:= stamp v.volW; let k':= T.whereAt Y Z R i (H v.volW)
    have hk: W_ i≤ k':= T.has_space _ _ _ _ _
    have hp : k'-W_ i ≤ q+1:= by
       have hw:=v.ok; change v.offset < W_ i at hw; change k'-W_ i≤ k'-(v.offset+1)+1; omega
    have hr:q+1≤ k'+W_ i:=by have he':= T.vert_j Y Z R stamp H v; change k'-v.offset=q+1 at he'; omega
    change (V).desk.pactP v = (f.op q N).patch
    -- explicit `Periodic op.patch=⟨ .. ⟩`
    unfold Oracle.Circuit.pactP Calendar.op
    congr
    · exact (T.steady Y Z R i (H _) _ hp hr).symm
    exact (T.enrol Y Z R i (H _) hp hr).symm
end Contract
end YM.RegulatorIR.FVAAlt2.Lodge
