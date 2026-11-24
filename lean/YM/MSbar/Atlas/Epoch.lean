import YM.MSbar.Atlas.Santa
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Stock
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f n':Side}{n:ℕ}{S:StepData c f}
open Precision Tree Pressure Push Push.AbsoluteSums ConnectedActivityE6 Push.Uniform
open Heath Bulk Finset
-- Numbers set for each {stage pair,p order}; look-ahead delays called eventually after L.
variable (P: Patch)(K : KernelChoices)(J:Voice G) (A B:Stage)(p:Palisade) 
set_option quotPrecheck false
local notation "L"=> P.L
local notation "Ξ"=> tip G L
-- Data includes actually priced masks. Uniform over shooting.W.LAW.Startup.V.ep.
structure FaceValue (B:Stage)(q:ℝ)(R: Rep G n') :Prop where
    support : R.p.supportExponent=B.supportExponent
    clip : R.clip=B.clip
    enough : 1<q
    beta : q/2 ≤ R.beta
    upper : R.beta ≤2*q
    threshold : R.p.threshold=temp q
    size : R.p.B=radiusB q
    lawful : R.Lawful B.width B.paths (lbt q) (ability q) 1
    decent : WilsonStartup.Decent R.clip R.p
variable {R:Rep G f}{Y: Rep G c}
def sizingW (K:KernelChoices):= 100000+16*K.penalty
structure Season (J:Voice G) (H K:Stage) (s:ℝ)(R:Rep G f) (Y: Rep G c) (W:StepData c f) (q:ℝ) : Prop where
    hull : FaceValue H s Y
    case_ : FaceValue K (tip G W.patch.L s) R
    taskEval : Y.eval = W.push R.beta R.eval
    bends : Bid.Larger (G:=G) W
    storm : Psalm W R Y.p.threshold q
    lights : Continuous R.eval
    shine U:0< R.eval U
    primal : MergeProof.Menu.Arsenal R
    cuff : Quasi R.eval (tip G W.patch.L s* sizingW W.kernel) -- define S'
-- chooser.Curvature.Corge
-- Draw.R.View tools geometry.
local notation "Vu"=> (represent (G:=G) (n:=c) ∘ tint G (Exterior.Body 1 c))
variable (i:S.Choices)(F : Forest S.ratio)
    (j:Key F G)(A B : Stage) (s:ℝ)(x:Positions (Primary c G))
-- bounds scalar tables.Conv.
def skirt (b:ℕ):ℕ := (b+b+1)^4
def belt (b:ℕ):ℕ:= skirt b * skirt (2*b)
def vestal (P:Patch)(b:ℕ):ℕ:= belt b *skirt (4*P.L.val+8)
def xBill (B:BudgetPoint)(q:ℕ)(w:ℝ) := Real.exp (B.supportExponent*q)*2*Real.exp ((q:ℝ)*w)
local notation "κ"=>tip G P.L s
local notation "t"=>radiusB κ
local notation "E!"=> stockMove G p κ
local notation "e"=> increments κ
local notation "d" => distance κ
def digits(G:Gauge)(p:Palisade)(x:ℝ):= Nat.floor (distance x/stockMove G p x)
local notation "N"=> digits G p κ
def rpay (x:ℝ):= -(x/8 * (increments x * distance x))
-- target.One constant parameter; Price specialized on any c f. user. relax gas.
def whale (p:Patch)(G:Gauge)(K:KernelChoices)(x U₀ a:ℝ) := a/4+compass p K G *( ((Lattice.box (macroR p)).card*(Fintype.card PlaqAxes:ℝ))*U₀)+ U₀ -- x unused
local notation "T'"=> hurry p (max (skies κ) (arch κ)) E! (2*winch κ)
abbrev panel (Q : Voice G)(ρ : ℝ) := max (ρ:ℝ) (4*Q.C*shade G*ρ)
structure Tinted (A B : Stage)(s:ℝ)(P:Patch)(K: KernelChoices)(p:Palisade)(J:Voice G)(R:Rep G f)(Y: Rep G c)(w F Δ:ℝ): Prop where
    room : 1 < tip G P.L s
    hues : let x:=tip G P.L s; ∀ t':ℝ, |t'|=increments x → Floss p J t' (steps G p x) (arch x) (winch x) (base J x) (ceiling x) (skies x) (stockMove G p x) (2*winch x) (radiusB x)
    bon : let x:= tip G P.L s; ((belt (radiusB x):ℕ):ℝ)*4*Fintype.card G.ColorIndex*(J.C*arch x)*steps G p x ≤ winch x
    walk : let x:=tip G P.L s; ∀ l:ℕ,l≤ skirt (radiusB x)→ outset R.p B.width B.paths (ability x) (lbt x) R.beta (radiusB x) l + R.beta*(hurry p (max (skies x) (arch x)) (stockMove G p x) (2*winch x)- increments x*distance x) ≤ rpay x
    cover : necklace P ≤ radiusB (tip G P.L s)
    root : shade G*skies (tip G P.L s) ≤ J.r
    holm : base J (tip G P.L s) ≤ Y.p.threshold
    rung : let x:=tip G P.L s; whale P G K x R.p.threshold (base J x) ≤ ceiling x
    update : ∀ {c f':Side} {S:StepData c f'}, S.patch=P→ S.kernel=K →let x:=tip G P.L s; Real.exp (ankle Y.p Y.clip A.width A.paths (ability s) (lbt s) (base J x) 1 Y.beta)*Real.exp (SectorNext.Vacuum.shellBill G S R.beta-R.beta*S.kernel.penalty*R.p.threshold^2/2)≤ Δ
    adapts : let x:=tip G P.L s; let b:=radiusB x; (1+Real.exp (x*sizingW K*(J.C*steps G p x)*(4*(skirt b:ℕ)) + R.beta*(stockMove G p x*p.noise)))*((belt b:ℝ)*(w+ 4*((Lattice.box (macroR P)).card*w+Δ)))+w*(xBill R.p (vestal P b) 1) ≤ F
variable (htb:S.patch=P)(hq:S.kernel=K)
open Metric Set
variable {β D E d₀:ℝ} (hm:Season J A B s R Y S D)(hb:Tinted A B s P K p J R Y D E d₀)
namespace Tinted
variable (h:Grants i R F p n)(g:Clear G J)
include g hb
lemma litV (W: ‖x‖ ≤ skies (tip G P.L s)) (r:ℝ)(hr: r=base J κ) (hs:0<r) : (Vu x) ∈ calm G c r:=by
    intro i _; let u:= Exterior.coord i.2; let y:=tint G _ x; let p:= shade G; let k' := shade G* skies (tip G P.L s); have he : ‖y‖ ≤k':= (tint_le x).trans (mul_le_mul_of_nonneg_left W (shade_pos G|>.le))
    change G.chord (G.lieExp (y (i.1,u)) * 1) ≤ _; rw [mul_one]; have hN:= (norm_le_pi_norm y (i.1,u)).trans he
    have hv: G.chord _ ≤ J.C*k' := ((g.small _ (hN.trans hb.root)).2).trans (mul_le_mul_of_nonneg_left hN (zero_le_one.trans g.cost))
    exact hv.trans (by unfold base at hr; unfold k'; linarith only [hr,hs])
include htb hq hm
lemma stencilSizes(W:‖x‖ ≤ skies κ) (H0 : 0 ≤ D)(hT:0<base J κ) (n₀:ℕ) (hZ:n₀=t):
    chance S R (Vu x) (excavation (G:=G) F (halo (2*n₀) (shutterPad F G j n₀)) R.p.threshold (ceiling κ))ᶜ ≤ belt (t:ℕ)*(D+4*((Lattice.box (macroR P)).card*D+d₀)) :=by
    let v:= Vu x; let k:= n₀; let X:= shutterPad F G j k; let Z:=halo (2*k) X
    obtain ⟨hA,hB,hq',hΩ,hξ,hg,hL,hF,hS⟩:=hm; rw [htb] at hB hS
    let hp:= hB.lawful; let hp' := hA.lawful
    have hs: v∈calm G c (base J κ):= litV _ _ _ _ _ _ _ _ hb g W _ rfl hT -- signature
    have he:= voids hs hb.holm; have HA:0 < S.push R.beta R.eval v:=by rw [←hq']; unfold Rep.eval; rw [Activities.gas_one _ _ he,mul_one]; exact Real.exp_pos _
    have hk:Admitted v R S B.width B.paths (ability κ) (lbt κ) 1:=⟨hp,fun i=>(hL i).le,HA,S.isKernel hΩ.1 _⟩
    have hC(l:Site f)(hy:l∈Z): chance S R v {U | l∈ RG.flags R.p.threshold U} ≤ D := by simpa using probability_flag v hk hξ he H0 l
    let k' := gCost R S D 1; let U:= (Lattice.box (macroR P)).card * D + d₀; have hK : 0 ≤ U:=by
         have hh : 0 ≤ d₀:= (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le).trans (hb.update htb hq); positivity
    have hu': 0 ≤ R.beta:=le_trans (by linarith [hB.enough]) hB.beta
    have hn:0 ≤ Y.beta:= le_trans (by linarith [hA.enough]) hA.beta
    have hy : Heath.brow S G (base J κ) R.p.threshold R.p.threshold ≤ ceiling κ := by unfold Heath.brow Heath.breeze; rw [htb,hq]; exact hb.rung
    have hv(i:F.Free)(ht:i.val.1∈ Z) : chance S R v {U:Config G f | ceiling κ < G.chord (canoe F U i.val)} ≤ U:=by
        let u:= Heath.brow S G (base J κ) R.p.threshold R.p.threshold
        let P(x:ℝ):={U:Config G f | x< G.chord (canoe (S:=S) F U i.val)}
        have hh(q):MeasurableSet (P q):=(isOpen_lt continuous_const (G.continuous_chord.comp ((continuous_apply i.val).comp (canoe_cont F)))).measurableSet
        refine (c_mono v hk (hh _) (hh u) (fun a hd=> hy.trans_lt hd)).trans ((around (V:=v) hk F i.val hp' hs hb.holm hT hA.decent hq' hΩ.2.1 hΩ.2.2 hn hΩ.1 R.p.threshold_pos.le hu' hξ H0).trans (add_le_add ?_ (hb.update htb hq)))
        unfold gCost; rw [htb,mul_one]
    have hT:X.card ≤ skirt k:= by simpa only [shutterPad, skirt,X,Finset.card_singleton,one_mul] using Corona.halo_size ({address F G (.inr j)}:Support f) k -- card one
    have hW: Z.card ≤ belt t:= by rw [←hZ]; have hh:= Corona.halo_size X (2*k); unfold belt skirt; apply hh.trans; exact Nat.mul_le_mul_right _ hT
    have hz:= shrinking F v hk _ (ceiling κ) Z hC (y:=D) (fun i hi=> hv i hi) hK
    refine hz.trans ?_; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hW) (add_nonneg H0 (mul_nonneg (by norm_num) hK))
end Tinted
end YM.MSbar.Heath.Stock
