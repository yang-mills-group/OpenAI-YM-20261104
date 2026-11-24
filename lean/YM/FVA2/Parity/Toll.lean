import YM.FVA2.Parity.Play
/-!
# Keep the parity on marks (`Relays`) through the limit

In particular on the `meteor` at the specified `MS_Data`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Parity.Invol
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open Hue.Agent Hue.Agent.Kappa
variable {d n m k e i j:ℕ}{G:Gauge}{f q:Cn}
local notation "σ"=> Hue.σ
local notation "ς"=> Screen.sigma
local notation "H"=> Press.portDeck G
local notation "M"=> FieldEnd G d
local notation "L"=> Guard G d
local notation "t₀"=> hinge d
local notation "V"=> Toon G d
local notation "Y₀"=> Labels.Key G
lemma starting (a:Toon G d) : t₀ (theory a)= σ a.grade • theory a:= by
    apply Subtype.ext; refine XSpace.Taylor.parity_sign _ ?_; apply (distilled_eq .. ).mpr; let C₀:= Press.beginning a.2.2 (w:=a.size); refine (Maxwell.Free.commuting (fun _:Y₀=> 1) (fun _=> ( 1:ℕ)) reduceEq (reduce_grade (fun _=> (1:ℕ))) C₀.val a.grade ).trans ?_; rw [ (Press.pure_count ( Press.primary a.2.2 (w:=a.size) )|>.weightedHomogeneousComponent_same ) ]; rfl
variable (ν:ℝ)(W: XSpace.Initialize G){P:Booked (Press.portDeck G) }(S:Prescription (Press.portDeck G))(T:MS_Data G P)
lemma good_g (C:XSpace.Mesh)(p:Toon G d)(a: Toon G p.size)(h: Screen.Right S): ς (n+a.grade+p.grade) * stake ν S C p a n = stake ν S C p a n:= by
    let v:=n+a.grade+p.grade; let Q:=( S.fees p.size (panel p) n).register; let E:= (Polynomial.eval (ν-Arrival.Schedule.theta C)); have hm: ( ς v • Q a ) = Q a := congr_fun (h.cost _ _ n) a; unfold stake ink; rw [mul_left_comm]; congr 1; exact (Polynomial.eval_smul ..).symm.trans (congr_arg E hm)
lemma goodStory (X:XSpace.Mesh)(p:V)(j:ℕ)(h:Screen.Right S) : σ p.grade • Dframe.story ν S X p j = σ j • hinge p.size (Dframe.story ν S X p j):= by
    unfold Dframe.story; rw [map_sum]; simp only [ Finset.smul_sum ]; refine Finset.sum_congr rfl fun i _=>?_; rw [show ∀ x:Sec G p.size, stake ν S X p i j • x=( (stake ν S X p i j:ℝ):ℂ ) • x from fun x=> ( IsScalarTower.algebraMap_smul ℂ _ x ).symm ]; rw [map_smul, starting,smul_smul,smul_smul,smul_smul ]; refine congr_arg (· • theory i) ?_ -- `_` binder?
    let a:=( ↑(stake ν S X p i j):ℂ); obtain ha₀:= congr_arg Complex.ofReal (good_g (n:=j) ν S X p i h); rw [Complex.ofReal_mul, Screen.sig, Hue.sp,Hue.sp] at ha₀; change _= a at ha₀; change σ p.grade * a = σ j * a*σ i.grade; nth_rw 1 [← ha₀]; calc
     _=(σ p.grade * σ p.grade)*(σ j*(a*σ i.grade)) := by ring
     _= _:= by rw [ Hue.s_id,one_mul,mul_assoc]
lemma birth (m:Mesh)(he: Screen.Right S) : Facing ( D ν S m d ):= by
    intro j p; rw [Dframe.pays,← all_sig p, map_sum, map_sum, map_sum,map_sum, Finset.smul_sum ]; refine Finset.sum_congr rfl (fun i _=>?_ ); let c:=( Daylight H d ).repr p i;
    have he(p:V): ( wold ν S m d j ) (t₀ (theory p))=σ j • t₀ ( wold ν S m d j (theory p) ):= by rw [ starting, map_smul,w_lit,hinge_up, ← _root_.map_smul, ← _root_.map_smul,goodStory ν S m p j he ]; -- rw order
    simp only [_root_.map_smul]; rw [starting, ← starting i,he]; exact smul_comm ..
-- relay on point and report simultaneously; no reality condition needed here
abbrev Relays (X:ℕ→Structure1.Point G d n) : Prop:= ∀ (i:ℕ)(v:Tags G d n),X i ( (hinge d) ∘ v )= Hue.σ i • X i v
namespace Relays
lemma pay {F:ℕ→ Structure1.Point G d n}(h:Relays F)(f:Cn)(hf:Anti f): Relays ( substitute f F ):= by
    intro i v; simp only [rules,_root_.sum_apply, _root_.smul_apply,h, Finset.smul_sum ]; refine Finset.sum_congr rfl (fun j _=>?_); by_cases hx:i%2=j%2; · rw [Hue.s_he.mpr hx,smul_comm (σ j)]
    unfold Program.cut; rw [hf.pairwise j i ( Ne.symm hx ),zero_smul,zero_smul,smul_zero ]
lemma meet {F:ℕ→ Structure1.Point G d n}{T:Guard G d}(h:Relays F)(ht:Facing T): Relays ( status T F ):= by
    intro i v; simp only [ seen, Finset.smul_sum ]; refine Finset.sum_congr rfl (fun k hk=>?_ ); let a j:= σ (k (some j)); let w:= pulseU k T v;
    rw [ show pulseU k T (t₀ ∘ v)=fun j=> a j • t₀ (w j) from funext fun x=> ht (k (some x)) (v x) ]; change F ( k none ) (fun i=> a i • ( (t₀ ∘ w) i )) = _; rw [ (F _ ).map_smul_univ a (t₀ ∘ w), h, smul_smul ]; obtain hh:∑ j: Option (Fin n),k j = i:= (totaled k).mp hk; rw [ Fintype.sum_option, add_comm ] at hh; unfold a Hue.σ; rw [Finset.prod_pow_eq_pow_sum, ← pow_add,hh]
lemma lit (y: Sample n): Relays ( live W d y ):= fun i p=> by rw [ ← Screen.sig ]; exact Rose.cooksO ..
lemma posted (m:Sample n)(h: Correct S.team)(hf: Screen.Right S): Relays (postedPoint ν W S d m):= meet (pay (lit W m) _ (Lambda.Pen.shifted S.team _ h)) ( birth ν S m.F hf )
end Relays
variable (h:G.Simple)(hs:TaylorOKF T (Press.wickInput W) S)
include h hs
lemma earns {x:Points n}(hx:x∈conf n): Relays (meteor ν T d x):= by
    let X:=Screen.brush S; have he := Screen.trueS W T S h hs; obtain ht:Correct X.team:= standardF h he
    intro i t; apply tendsto_nhds_unique (f:=fun y:Sample n=> postedPoint ν W X d y i (t₀ ∘ t)) ( tB ν W X T h he i (t₀ ∘ t) x hx ); apply Tendsto.congr (fun i=>?_) (( tB ν W X T h he i t x hx ).const_smul (σ i)); exact (Relays.posted ν W X i ht (Screen.verifiedS S) _ t).symm -- i binder!
open Reg.CoverTest
lemma headed : Normalize.Forward (Reg.State.kernel ν T d):= by
    intro i; ext1 n; ext1 t; ext1 v; rw [recruits]; change Rates ν T d i n t (t₀ ∘ v)= ( Screen.sigma i) • Rates ν T d i n t v; rw [indicative, indicative ]; let u x:= meteor ν T d x i v; rw [show t.applyTo (fun x=> (meteor ν T d x i) (t₀ ∘ v))=t.applyTo (fun x=> σ i • u x) from Test.apply_eq t (fun x hx=> earns ν W S T h hs hx i v) ]; unfold Test.applyTo u; simp_rw [smul_eq_mul, mul_left_comm _ (σ i) ]; rw [integral_const_mul, ← Screen.sig ]; rfl
lemma frameForms (S':Normalize.Store G): Facing (Reg.State.chooseL ν S' T d):= by
    refine Wants.now _ ?_; exact Reg.State.near_free ν S' T _ (by rw [faced,Reg.State.baseK,map_zero,smul_zero]) ( solve_arch (S'.prepared d) _ _ ( headed ν W S T h hs ) ( Reg.State.success ν S' T|>.2.1 ) )
end YM.FVA2.Parity.Invol
