import YM.SignedWilsonExpansion.Grid.Pay
import YM.SignedWilsonExpansion.OrderHigh
namespace YM.SignedWilsonExpansion.Overlap.Align
/-! Exchange two spatial axes, independent cardinal proof on fees (not
transverse-symmetric property of unprojected regulated momentum extension).
`pay_value` charges both orientations by chosen mark ⋔-cost; normalization
field E12, mark projected from 12 to 02 and reciprocally. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView HighRank HighScale MarkRows AxisChoice
open MassShift MarkShift TraceE TorchE
open Energy (leg) -- may syntax
open Gaussian Curtain
open scoped Classical Topology ContDiff BigOperators
local notation "Z" => Momentum.sq
local notation "P" => FourP
local notation "μ" => covMeasure Axis
local notation "A" => Axis
variable (σ: Equiv.Perm Axis) (h:ℝ→ℝ)(p q r:P)(a b i j k u v:A)
local notation "B" => receive σ
-- p remapped by B as contravariant on axes.
lemma same (p:P): Z (B p)= Z p:= Curtain.permute_sq σ _
lemma funP (a:A)(p:P): (B p) a=p (σ a):= rfl
lemma flipped : B (-p)= -(B p):= rfl
lemma plus : B (p+q)=B p+B q:= rfl
lemma diff : B (p-q)= B p - B q:= rfl
lemma coin (t:ℝ) : B ( t • p )= t • B p:= rfl
lemma legL : leg a b i (B p)=leg (σ a) (σ b) (σ i) p:= by simp [ Energy.leg, funP ]
lemma upKr : Landau.delta a b=Landau.delta (σ a) (σ b):= by funext c; simp [ Landau.delta ]
lemma upR : Slice.delta a b=Slice.delta (σ a) (σ b):= by simp [ Slice.delta ]
lemma lap : precision a b ( B p )= precision (σ a) (σ b) p:= by simp only [precision, ← upKr σ, Align.same,funP]
lemma cole : bond h ( B p ) a b=bond h p (σ a) (σ b):= by simp only [bond, Align.same,lap]
lemma paving : play a b i j= play (σ a) (σ b) (σ i) (σ j):= by simp only [play,← upR σ]
lemma reached : sideV a b i j= sideV (σ a) (σ b) (σ i) (σ j):= by simp only [sideV,← upR σ]
lemma D4V : h0 a b i j=h0 (σ a) (σ b) (σ i) (σ j):= by simp only [h0,← reached σ]
def Award (V W:A→A→A→P→P→P→ℝ)(σ:Equiv.Perm Axis): Prop := ∀ i j k p q r,V i j k (receive σ p) (receive σ q) (receive σ r) = W (σ i) (σ j) (σ k) p q r
lemma pay_rib : Award Slice.rib Slice.rib σ:= by intro i j k p q r; simp only [Slice.rib, ← upR σ, Pi.sub_apply, funP]
lemma pay_mark : Award (yMark a b) (yMark (σ a) (σ b)) σ:= by intro i j k p q r; simp only [yMark,legL,← paving σ]
lemma pay_paint : paint h (B p) a b i=paint h p (σ a) (σ b) (σ i):= by unfold Bubble.paint; rw [ same,legL] -- twice same maybe
lemma sum2 (f:A→A→ℝ): (∑ i:A,∑ j:A,f (σ i) (σ j))=(∑ i:A,∑ j:A,f i j):= by
    conv_rhs=> rw [ ← Equiv.sum_comp σ ]
    exact Finset.sum_congr rfl fun i _=> Equiv.sum_comp σ _
lemma pay_feather (t:P) (V W:A→A→A→P→P→P→ℝ)(hp: Award V W σ) : feather V h u i v j (B p) (B q) (B r) ( B t )= feather W h (σ u) (σ i) (σ v) (σ j) p q r t:= by unfold feather; simp_rw [ ← plus, ← flipped, cole, pay_rib σ _ _ _ p, hp _ _ _ r ]; apply congr_arg; rw [← sum2 σ (fun l m=> bond h (p+q) l m*Slice.rib (σ u) (σ i) l p q (-(p+q))*W (σ v) (σ j) m r t (p+q)) ]
lemma pay_c (k X:P) : Bubble.center h a b u i v j (B k) (B p) (B r) (B q) (B X)= Bubble.center h (σ a) (σ b) (σ u) (σ i) (σ v) (σ j) k p r q X:= by simp only [Bubble.center, ← plus,← diff, ← flipped,pay_rib σ _ _ _ k,pay_rib σ _ _ _ r q,pay_paint]; rw [ ← sum2 σ (fun l m=>Bubble.paint h (k+p) (σ a) (σ b) l * Bubble.paint h (k+p-X) (σ a) (σ b) m*Slice.rib (σ u) (σ i) l k p (-(k+p))*Slice.rib (σ v) (σ j) m r q (k+p-X)) ]
lemma pay_leaf (k X:P) : leafPrice h a b i j u v (B p) (B q) (B k) (B X)= leafPrice h (σ a) (σ b) (σ i) (σ j) (σ u) (σ v) p q k X:= by unfold leafPrice; simp_rw [← flipped, pay_feather σ h _ _ _ _ _ _ _ _ _ _ (pay_mark σ a b), pay_c ]
lemma pay_body (k X:P) : body h u v i j (B k) (B p) (B X) (B q)= body h (σ u) (σ v) (σ i) (σ j) k p X q:= by
    unfold body; simp_rw [pay_feather σ h _ _ _ _ _ _ _ _ _ _ (pay_rib σ)]; rw [ D4V σ u v i j ]
-- precise reorder and finish
lemma inspection (k:P): TraceE.complete h a b (B p) (B q) i j (B k)= TraceE.complete h (σ a) (σ b) p q (σ i) (σ j) k:= by unfold TraceE.complete; simp_rw [ ← plus, ← flipped, ← diff,lap, legL, same, pay_paint, pay_body, pay_leaf ]; rw [ ← sum2 σ (fun u v=>precision u v k*leafPrice h (σ a) (σ b) (σ i) (σ j) u v p q k (p+q)), ← sum2 σ (fun u v=> 4*Z k*leg (σ a) (σ b) u k * Bubble.paint h (k+(p+q)) (σ a) (σ b) v*body h u v (σ i) (σ j) k p (-k-(p+q)) q) ]
variable {G:Gauge}{O:Land.Booked (Press.portDeck G)}(M: MS_Data G O)(η:G.Simple)(C:G.ColorIndex)(x t:ℝ)
lemma all_cost (k:P): rawE t (B k) a b G i j (B p) (B q)= rawE t k (σ a) (σ b) G (σ i) (σ j) p q:= by unfold rawE; simp only [Align.same, ← flipped,inspection]
local notation "ι" => Equiv.swap (0:Axis) 1
local notation "D" => receive (Equiv.swap (0:Axis) 1)
variable (s s':Bool)
-- orientation 1,2 positive. θ measure. Opposite via permuting genuine recu.
abbrev degreeX (s:Bool): Axis:= if s then 1 else 0
def vane (s i:Bool) : Axis:= if i then 2 else degreeX s
def tune (s i:Bool) : P:= if i then unitV (degreeX s) else -unitV 2
abbrev tested (m:Bool) (F: Law G):ℂ:= ∑ i:Bool,∑ j:Bool,(1/2:ℝ) • ( torch 2 F [W (vane m i) C (tune m i),W (vane m j) C (tune m j)]- torch 2 F [ W (vane m i) C (tune m i),W (vane m j) C ( -tune m j ) ] )
local notation "ξ" => Energy.called
local notation "φ" => recu (spaceD G)
local notation "K2" => fun (m:Bool)=>MarkRows.packet M (Energy.called (degreeX m) 2 G)
abbrev attic (s:Bool) (X:Clock ℝ) : Law G:= recu (spaceD G) 0 1 (Archive 4 M.bulk) (K2 s) 2 X
lemma bore : degreeX (!s)=ι (degreeX s):= by cases s <;> rfl
lemma bore2 : (ι (2:Axis))= (2:Axis):= rfl
lemma tips : vane (!s) s'=ι (vane s s'):= by cases s <;> cases s' <;> rfl
lemma turret : tune (!s) s'=D (tune s s'):= by funext i; unfold tune; cases s <;> cases s' <;> fin_cases i <;> simp (disch:=decide) [Curtain.receive,unitV,spike,Equiv.swap_apply_def,degreeX]
lemma flipB (p:P): D (D p)=p:= by unfold Curtain.receive; funext i; simp
include η M
lemma recuL (X:Clock ℝ): torch 2 (attic M s X) [ W i C p,W j C q ]=
    torch 2 (attic M (!s) X) [ W (ι i) C (D p), W (ι j) C (D q) ]:= by
    rw [ attic, attic, TorchE.projector M η X,TorchE.projector M η X, ← (Curtain.sameM ι).integral_comp ( Curtain.receiveE ι) (fun k:P=>reading 2 (fun t=>rawE X.2 k (degreeX s) 2 G i j (t • p) (t • q))) ]; -- have all_cost…
    apply integral_congr_ae; apply Eventually.of_forall; intro k; dsimp only; congr 1; funext t
    obtain he:= all_cost (G:=G) ι (t • D p) (t • D q) (degreeX s) 2 i j X.2 k; rw [coin, coin ι (D q), flipB, flipB, bore2, ← bore] at he; exact he
omit M η in
lemma tested_false (F:Law G): tested C false F= assayAct C F:= rfl -- maybe tune.simplifies
lemma clocked (X:Clock ℝ) : tested C s' (attic M s X)= tested C (!s') (attic M (!s) X):= by
    unfold tested; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_ ; rw [ tips s',tips s', turret s', turret s', recuL _ _ _ _ M η C s, recuL _ (-tune s' j) _ _ M η C s, flipped ]; -- args
local notation "ν" => (2*b₀*G.casimir)
local notation "Κ" => ((-8:ℂ))
lemma toll (X:ℝ): tested C (!s) (attic M s (X,0))= Κ*( (2*b₀*G.casimir:ℝ):ℂ ):= by
    have ht: tested C false (attic M true (X,0))=Κ*( (2*b₀*G.casimir:ℝ):ℂ ):= by change assayAct C (Radial.trigger M _) = _; rw [ Curtain.paycheck M η C X ]; push_cast; ring
    cases s
    · exact ( clocked M η C false true (X,0) ).trans ht -- fix order
    exact ht
-- use static transfer back `Cost(t)` and scale v
local notation "z" => fun m=> MarkShift.settled M (ξ (degreeX m) 2 G) t
open OrderHigh
lemma static2 (i:Bool) : Static ( z i ) 2 4 false:=bridge_static M ( ξ (degreeX i) 2 G ) η _ Energy.full t
-- need sparse wall polynomial derivative smooth `OrderHigh.wall_p` private copy
omit η in
private lemma clean_wall : Polish (wall M t):= by
    intro E _ _ w; by_cases he:w.length=2
    · have hx: fieldVal (wall M t) w=fieldVal (leap t (bulkD M) (0,0)) w:= funext fun x=> Book.enough _ (by simp [he])
      rw [hx]; exact (hair (bulkView M 2 (by omega)|>.host) (n:=0) (y:=0+t) (s:=0) w).sub (hair (bulkView M 2 (by omega)|>.host) (n:=0) (y:=0) (s:=0) w)
    rw [show fieldVal (wall M t) w=0 from funext fun x=> Book.strange _ (show ((sail w x).length:ℤ) ≠ 2 from by rw [sail_len]; omega)]; exact contDiff_const
omit η in
lemma settle (s:Bool) :
    let w:=[W i C p,W j C q]
    torch 2 (z s (0,0)) w=torch 2 ( K2 s 2 (0+t,0)) w - torch 2 ( K2 s 2 (0,0)) w:= by
    let m:=ξ (degreeX s) 2 G
    intro w; let F:=bridge M m t 0; have he:TorchE.emptyR (fun u=>F (sail (ray w) u)):= by unfold F MarkShift.bridge m; rw [Energy.found,Walk.ampL]; exact TorchE.skipH ( clean_wall M t ) TorchE.smooth_amp
    let c x:=fieldVal ( packet M m 2 ( x,0 )) ( ray w ); let T:=leap t (packet M m 2) (0,0); have hm x: ContDiff ℝ ∞ (c x):= MarkRows.polish M m _ _ ℝ _
    rw [ show z s (0,0)= T-F from rfl,High.Knobs.torch_sub (M:=T) (W:=F) w ( ( hm (0+t) ).sub (hm 0) ) he.smooth, show torch 2 F w=0 from he.read _ (by decide), sub_zero ]; exact High.Knobs.torch_sub w ( hm (0+t) ) ( hm 0 ) 2
lemma heat : HasDerivAt (fun t=> tested C (!s) ( K2 s 2 (t,0) )) ( Κ*( (2*b₀*G.casimir:ℝ):ℂ ) ) x:= by
    rw [ ← toll M η C s x ]; refine HasDerivAt.fun_sum fun i _=> HasDerivAt.fun_sum fun j _=> ?_
    have he(p q:P): HasDerivAt ( fun t=> torch 2 ( K2 s 2 (t,0) ) [ W (vane (!s) i) C p,W (vane (!s) j) C q ] ) (torch 2 (attic M s (x,0)) [W (vane (!s) i) C p,W (vane (!s) j) C q]) x :=shear_derivative ( sheared M (Energy.called (degreeX s) 2 G) 2 2) _ (fun v=> Bool.noConfusion v) rfl 2 rfl (MarkRows.speed M _ 2 _) _ _
    exact ( ( he _ _ ).sub (he _ _) ).const_smul (1/2:ℝ)
abbrev salaryQ (G: Gauge) :ℝ:= 2*b₀*G.casimir
lemma pay_value : tested C (!s) ( z s (0,0) )= Κ*( (t*salaryQ G:ℝ):ℂ ):= by
    obtain he:= OrderHigh.difference 0 t _ _ (fun t=> heat M η C t s)
    unfold tested; simp_rw [ settle (p:=_) (q:=_) (i:=_) (j:=_) M C t ]; unfold tested at he; rw [ ← Finset.sum_sub_distrib ] at he; simp_rw [← Finset.sum_sub_distrib] at he; convert he using 1
    · refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; module
    · unfold salaryQ; rw [Complex.real_smul]; push_cast; ring
end
end YM.SignedWilsonExpansion.Overlap.Align
