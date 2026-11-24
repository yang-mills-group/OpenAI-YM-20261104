import YM.FormalOPE.RG10.Carryon.Return

/-! Any-arity producer via convergence of an auxiliary reparametrized system; include a
 common substitution across *all arities* on regulators. Allows using another (proved equivalent)
 constructive scheme internally to get position/coupling convergence. Note no rates, and no
 claim that `Extra` is the needed perturbative theorem itself. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Peal
variable {G : Gauge} {F : Frames G} {d : ℕ}
local notation "V" d=> Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "K" d => Matrix (Deck F d) (Deck F d) fps
local notation "L" d=> Matrix (Deck F d) (Deck F d) ℝ
abbrev Rack (F:Frames G):= ∀ d,Mark (Deck F d) PertExtension.Physical.Profile.n→fps
def Row (u:Rack F) (D:Stock F) : Rack F:= fun i=> post D (u i)
def Init (u:Rack F)(D:Stock F) : Rack F:= fun i=> (D i).positioned (u i)
def Convention (u:Rack F):= charged (u 6)
def mintRack (u:Rack F) : Rack F:= fun i=> (Convention u).refund.charge ∘ u i

def extra (u:Rack F)(p:Warp)(X:∀ i:ℕ,K i) : Rack F:= fun i=> PertExtension.Position.insert _ PertExtension.Physical.Profile.n (p.charge ∘ u i) (X i)
def Eligible (v:Rack F)(Y:Drivers)(f:ℕ+→ℕ→Rack F) := ∀ i j,Y.Credit (fun a b => f a b i j) (v i j)
structure Invitation {u:ℕ+→ℕ→Rack F} (Y:Drivers)(D:Stock F)
    (p:ℕ+→ℕ→Warp)(X:ℕ+→ℕ→ ∀ i:ℕ,K i)(v:Rack F) : Prop where
 order : Official D
 prepared (q:ℕ+)(m i:ℕ) : Upright (X q m i)
 landing (i:ℕ) : ∀ᶠ q in Y.ages,Tendsto (fun j=> Stg (X q j i) 0) atTop (𝓝 (1:L i))
 valid : (Convention (Init v D)).Hot
 purchased : Eligible v Y (fun i j=>extra (u i j) (p i j) (X i j))
 hand (i j) : constantCoeff (v i j)= raw F i j
namespace Eligible
variable {v:Rack F}{Y:Drivers}{f:ℕ+→ℕ→Rack F}{D:Stock F}(h:Eligible v Y f)
include h
lemma told (i:ℕ) (hp:∀ j,constantCoeff (v i j)= raw F i j) : ∀ᶠ q in Y.ages,listens (l:=atTop) (D:=D) (fun j=> f q j i):= by
 filter_upwards [eventually_all.mpr (show ∀ j, Y.Harvest _ (coeff 0 (v i (markIn (D i).tests j))) from fun j=> h i _ 0)] with q hx
 apply tendsto_pi_nhds.mpr; intro t; simpa only [probe,Function.comp_apply,coeff_zero_eq_constantCoeff_apply,hp] using hx t
lemma totals : Y.Credit (fun i j=>(Convention (f i j)).x) (Convention v).x:= Drivers.Tasks.collected (h 6)
lemma serve (hv:(Convention v).Hot) : Eligible (mintRack v) Y (fun i j=> mintRack (f i j)):= fun _ _=> crossing (returning (p:=fun i j=> Convention (f i j)) (q:=Convention v) h.totals hv) (h _ _)
end Eligible
namespace Invitation
variable {u:ℕ+→ℕ→Rack F} {Y:Drivers}{D:Stock F}
    {p:ℕ+→ℕ→Warp}{X:ℕ+→ℕ→ ∀ i:ℕ,Matrix (Deck F i) (Deck F i) fps}{v:Rack F}
variable (t:Invitation (u:=u) Y D p X v)
local notation:max "aux[" i ", " j "]" => extra (u i j) (p i j) (X i j)
include t
lemma near (i:ℕ) : ∀ᶠ q in Y.ages,listens (l:=atTop) (D:=D) (fun j=> u q j i) := by
 filter_upwards [t.purchased.told (D:=D) i (t.hand i), t.landing i] with q hp hk
 apply (show _ from forward hk hp).congr
 intro b; funext j; exact (p q b).smoothed _
lemma credible (i:ℕ): ∀ᶠ q in Y.ages, ∀ᶠ m in atTop,Credible D (u q m i):=(t.near i).mono fun _ hk=> credential t.order _ hk
lemma notice : Eligible (Init v D) Y (fun i j=> Row (aux[i,j]) D):=fun d j=>lighten t.order (t.hand d) (t.purchased d) j
lemma link (i:ℕ) : ∀ᶠ q in Y.ages, ∀ᶠ m in atTop, Row (aux[q,m]) D i= (p q m).charge ∘ Row (u q m) D i := by
 filter_upwards [t.purchased.told (D:=D) i (t.hand i), t.landing i,t.credible i] with q hp hk hl
 filter_upwards [loading t.order (fun s=> X q s i) (b:=fun j=>(p q j).charge ∘ u q j i) (forward hk hp) (fun a=> t.prepared _ a _) hk hp, hl] with a ha hx;
 exact ha.trans ((p q a).publish t.order hx)
lemma decided : ∀ᶠ q in Y.ages, ∀ᶠ m in atTop, Convention (Row (aux[q,m]) D)= (p q m).step (Convention (Row (u q m) D)) := (t.link 6).mono fun i hi=> hi.mono fun m hu=> by
 change charged _=_; rw [hu]; exact Warp.trade ..
lemma hot : ∀ᶠ q in Y.ages, ∀ᶠ m in atTop, (Convention (Row (u q m) D)).Hot ∧ (p q m).Hot:= by
 filter_upwards [t.notice.totals 1,t.decided] with q hx hv
 filter_upwards [hx.eventually (isOpen_compl_singleton.mem_nhds t.valid),hv] with m hm hn
 change (Convention (Row _ _)).Hot at hm; rw [hn,Warp.flames] at hm; exact hm.symm
lemma fulfilled : Eligible (mintRack (Init v D)) Y (fun i j=>mintRack (Row (u i j) D)) := by
 intro n v' k;
 apply (t.notice.serve t.valid _ v' k).along rfl; filter_upwards [t.link n,t.link 6,t.hot] with q hn h6 ht
 filter_upwards [hn,h6,ht] with m hm hw hp; apply congr_arg (coeff k); unfold mintRack Convention; rw [hm,hw]; exact Warp.trading _ _ hp.1 hp.2 _

-- can recover the conventional bare funding coordinate when change of variables has
-- a finite nonzero leading *limit* at every late controller. For additional tasks use `fulfilled` instead,
-- so can even regularize by a new parameter with *decaying* stakes if applicable.
lemma pace {x:ℝ}(hx:x≠0)(hh:Y.Harvest (fun q m=> coeff 1 (p q m).x) x): Y.Harvest (fun q m=> coeff 1 (Convention (Row (u q m) D)).x) (coeff 1 (Convention (Init v D)).x/x):= by
 unfold Drivers.Harvest
 filter_upwards [hh, t.notice.totals 1,t.hot,t.decided] with q hx' ht hj ha
 apply (ht.div hx' hx).congr'; filter_upwards [hj,ha] with m h1 h2
 simp only [Pi.div_apply]; rw [h2, Warp.step,Warp.heats]; exact mul_div_cancel_right₀ _ h1.2
end Invitation
end YM.FormalOPE.RG10.Carryon
