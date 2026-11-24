import YM.FVAAlt2.Convert.Stages
/-!
# Finite-order POSE permit. For the moving surveys we proved strong estimates of **arrays after the necessary D and Φ corrections**. Show the existence onto same near-free branch and no multiplication by divergent bare reconstruction tensors. To turn normalized coefficient banks late, `Warp` only tested coefficientwise (despite definition by entire series, Frame operations, etc., convergence here needs only through r). Credence root in approximated lead.Frame receipts maybe not symmetric; Engine allows via Official.Start measuring inspector exact stencil-coordinate certificates and leading pose solve. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Moving.Budget
open Function Set Filter Finset FormalOPE FormalOPE.RG10 Position Carryon Gazebo PertExtension MeasureTheory Topology Metric PertExtension.Position PertExtension.Physical Labels Source Extra.FD Maxwell Extraction
open Lattice Precision Home Home.Report Triangle Convert
open PowerSeries (C coeff constantCoeff)
open MS.Land
open scoped Topology BigOperators ContDiff Interval PowerSeries Matrix Classical
variable {d r:ℕ} {G:Gauge}{F:Frames G}{X Y:Type}{l:Filter X}
local notation "PSc"=> PowerSeries ℂ
local notation "PS"=> PowerSeries ℝ
local notation "V_" i:max=> RG10.Position.Deck F i
abbrev Nice (r:ℕ)(l:Filter X)(v:X→ PowerSeries ℝ)(p: PowerSeries ℝ): Prop:= ∀ i≤ r,Tendsto (fun j=> coeff i (v j)) l (𝓝 (coeff i p))
section Weight
variable {v u:X→PS}{f g:PS}
lemma Nice.event (h:Nice r l v f)(hv:v =ᶠ[l] u): Nice r l u f := fun i hi=> (h i hi).congr' (hv.mono fun _ ht=> congr_arg (coeff i) ht )
lemma Nice.down (h:Nice r l v f){d:ℕ}(he:d≤r): Nice d l v f:= fun i hi=> h i (hi.trans he)
lemma Nice.asc (h:AlignSeries l v f): Nice r l v f:=fun i _=> h i
lemma Nice.edit (h:Nice r l v f)(he: ∀ x,Through r (v x) (u x)): Nice r l u f := fun i hi=> ( h i hi ).congr fun x=> he x i hi
lemma Nice.copyH (h:Nice r l v f): AlignSeries l (fun i=> Carryon.up r (v i) f) f:= aligning _ fun i hi=> h i (Nat.le_of_lt_succ (mem_range.mp hi))
lemma Nice.fore (h:Nice r l v f)(hk:Nice r l u g): Nice r l (fun i=>v i*u i) (f*g):= Nice.edit (Nice.asc ( h.copyH.mul hk.copyH )) (fun x=> (Carryon.copy r (v x) f).mul (Carryon.copy r (u x) g))
lemma Nice.sum [Fintype Y]{F:Y→ X→ PS}{f:Y→ PS}(h:∀ i,Nice r l (F i) (f i)): Nice r l (fun x=>∑ i,F i x) (∑ i,f i):= by
 intro i hi; simp_rw [map_sum]; exact tendsto_finsetSum _ fun j _=> h j _ hi
lemma Nice.use {J K:Type}[Fintype J][Fintype K]{A:X→Datum J→ PS}{a:Datum J→ PS}(h:∀ i,Nice r l (fun x=>A x i) (a i))(p:Matrix K J PS)(s:Datum K): Nice r l (fun i=> mix (A i) p s) (mix a p s):= Nice.sum (Y:=Fin s.1.n→J) fun v=> Nice.fore (h ⟨s.1,v⟩) (Nice.asc (AlignSeries.const _))
end Weight
section positionR
variable (P:Plan F)(ho:Official P.stock){f:Rack F}{u:X→Rack F} {Xw:X→Warp} {A:X→ ∀ i:ℕ,Matrix (Deck F i) (Deck F i) PS}
local notation "D!"=> P.stock
-- ∀ formal horizons masks in Stock. Truncate proof data (not the Limit on the stencil history) to apply full analytic lemma; extension by limit at higher horizon irrelevant.
lemma boundMark (P:Plan F) (h:Official P.stock)(hc:∀ s,constantCoeff ( f d s )= raw F d s)(hh:∀ s,Nice r l (fun i=>u i d s) (f d s) )(v:Home.Datum (Deck F d)): Nice r l (fun i=> Row (u i) P.stock d v) (Init f P.stock d v):= by
 let g(i:X)(s:Datum (Deck F d)):= Carryon.up r (u i d s) (f d s)
 let p:=f d; let Z:= P.stock d
 have H : (fun v=> constantCoeff ( p v ))= raw F d:= funext hc; have hK:Z.Regular (fun v=>constantCoeff (p v)):= H ▸ h.fresh d
 have hT:= (Z.positions_align p g hK (fun s=> (hh s).copyH) v)
 -- `Row¨post` selected around standard raw. limit exactly positioned.
 have hr(i:X): Z.systemAt p g i= crib P.stock (g i):= congr_arg (fun y=> Z.leadingAdjust y (fun v=> constantCoeff (g i v))) H
 apply (Nice.asc hT).edit; intro i; change Through r (( Z.systemAt p g i ).positioned _ _) _; rw [ hr ];
 have ht(j): Sync r (g i) (u i d) j:= fun _=> Carryon.copy r _ _
 exact Carryon.posting (fun i _=> ht _) v.1 (ht _) v.2
local notation "V"=> (fun x=> extra (u x) (Xw x) (A x))
def Preparation (r:ℕ)(l:Filter X)(_:Plan F)(T:X→ Warp)(A:X→∀ i:ℕ,Matrix (Deck F i) (Deck F i) PS)(u:X→Rack F)(w:Rack F):Prop:= (∀ i j,Upright (A i j))∧ (∀ d:ℕ,Tendsto (fun a=> Stg (A a d) 0) l (𝓝 1)) ∧ (∀ i s,constantCoeff ( w i s )= raw F i s) ∧ (∀ d x,Nice r l (fun i=> extra (u i) (T i) (A i) d x ) (w d x))
variable (m:Preparation r l P Xw A u f)
include m ho
lemma heard (d:ℕ): Carryon.listens (D:=P.stock) (l:=l) (fun s=> (u s) d) ∧ (∀ᶠ x in l, Row ( V x ) P.stock d=(Xw x).charge ∘ Row (u x) P.stock d):=by
 obtain ⟨hu,hT,hp,hQ⟩:=m
 have ht : Carryon.listens (D:=P.stock) (l:=l) fun s=> V s d:= by
    refine tendsto_pi_nhds.mpr fun i=>?_ ; have hz:= hQ d ( markIn _ i ) 0 ( Nat.zero_le _) ; simpa only [Carryon.probe,Function.comp_apply,PowerSeries.coeff_zero_eq_constantCoeff_apply,hp] using hz
 have hf: Carryon.listens (D:=P.stock) (l:=l) fun s=> ( Xw s ).charge ∘ (u s d):= forward (hT d) ht
 have he : Carryon.listens (D:=P.stock) (l:=l) fun s=> u s d := hf.congr fun a=> funext fun i=> Warp.smoothed ..
 refine ⟨he, ((Carryon.credential ho _ he).and (loading ho (fun x=>A x d) hf (fun x=>hu x d) ( hT d ) ht)).mono ?_ ⟩; exact fun t hs=> hs.2.trans (Warp.publish _ ho hs.1)
lemma quoted (d:ℕ) (v:Home.Datum (Deck F d)): Nice r l (fun i=> Row ( V i ) P.stock d v) (Init f P.stock d v):= boundMark P ho (m.2.2.1 d) (m.2.2.2 d) _
-- coupling normalization tests & exact cancellation. don't require numerical trajectory scheme realized. period λ.θ
omit m ho
private lemma touches {f v:Rack F}(h:∀ s,Through r (f 6 s) (v 6 s)): Through r (Convention f).x (Convention v).x:= by
 have hp:= First.Portray.together_through (p:=f 6) (q:=v 6) h; have hr:= hp 0 ( Nat.zero_le r ); rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_zero_eq_constantCoeff_apply] at hr
 apply Through.mul (Through.refl _); unfold Triangle.deviation; rw [hr]; exact hp.sub (Through.refl _)
private lemma inputs {T:Rack F} {u':X→Rack F}(h:∀ s,Nice r l (fun i=> (u' i) 6 s) (T 6 s) ): Nice r l (fun i=> ( Convention (u' i) ).x) (Convention T).x:=by
 let a(i:X): Rack F:= fun d s=> Carryon.up r ( u' i d s ) ( T d s ); exact (Nice.asc ( Convert.beatCost (b:=fun i=> a i 6) (a:=T 6) (fun v=> (h v).copyH) )).edit (fun i=> touches (f:=a i) (v:=u' i) (fun _=>Carryon.copy r _ _))
lemma fund_money {f: Warp}{p:X→ Warp}(H: Nice r l (fun i=>(p i).x) f.x)(hp:f.Hot){a:PS}{u:X→PS}(h:Nice r l u a): Nice r l (fun i=> (p i).refund.charge (u i)) ( f.refund.charge a ):=by
 let x(j:X):= ( p j ); let g(j:X):Warp:= ⟨Carryon.up r (x j).x f.x, ((PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm.trans ((Carryon.copy r (x j).x f.x _ (Nat.zero_le _)).trans ((PowerSeries.coeff_zero_eq_constantCoeff_apply _).trans (x j).atOrigin)))⟩
 let v(i:X):= Carryon.up r (u i) a; have hc(i: X): Through r (g i).x (p i).x:= Carryon.copy r _ _ -- supply
 have hs:= ( show AlignSeries l (fun i=> (g i).x) _ from H.copyH ).inverse_est (isUnit_iff_ne_zero.mpr hp)
 have he:AlignSeries l (fun i=>(g i).refund.charge (v i)) (f.refund.charge a):= by intro i; simp_rw [Warp.turning]; exact AlignSeries.compose hs (h.copyH) (PertExtension.Position.Triangle.inverse_zero _) (Eventually.of_forall fun _=> PertExtension.Position.Triangle.inverse_zero _) i -- use shape
 exact (Nice.asc he).edit fun i=>Warp.charges (p:=(g i).refund ) (q:=(p i).refund) ( Carryon.copy r _ _ ) (Warp.either (p:=g i) (q:=p i) (hc i)) -- binder order?
include ho m
local notation "R!"=> (fun i=> Row (u i) P.stock)
local notation "S!"=> Init f P.stock
local notation "χ"=> Convention ∘ (fun i=> Row ( V i ) P.stock)
lemma pre_slope (h : coeff 1 ( Convention (Init f P.stock)).x=1)(ht:r≠0)(he:∀ i,coeff 1 (Xw i).x=1): Tendsto (fun i=> coeff 1 (Convention (R! i)).x) l (𝓝 1):=by
 have hh:= ( inputs (T:=Init f P.stock) (u':=fun i=> Row ( V i ) P.stock) (fun v=> quoted P ho m 6 v) ) 1 ( Nat.pos_of_ne_zero ht ); rw [h] at hh; refine hh.congr' ?_; filter_upwards [( heard P ho m 6 ).2] with i hi; unfold Convention; rw [hi,Warp.trade, Warp.step,Warp.heats, he, mul_one] -- or one_mul
variable (h:coeff 1 ( Convention (Init f P.stock)).x=1)(ht:0<r)(he:∀ i,coeff 1 (Xw i).x=1)
include h ht he
lemma readyK : ∀ᶠ i in l,( Convention ( Row (u i) P.stock ) ).Hot:= (pre_slope P ho m h ht.ne' he).eventually (isOpen_ne.mem_nhds (one_ne_zero : (1:ℝ)≠0 ))
lemma chosen (d:ℕ) (v:Home.Datum (Deck F d)): Nice r l (fun i=> mintRack (Row (u i) P.stock) d v ) (mintRack (Init f P.stock) d v):= by
 let p(i:X): Rack F:= Row ( V i ) P.stock
 apply (fund_money (r:=r) (p:=Convention ∘ p) (inputs (u':=p) (quoted P ho m 6)) ( h.trans_ne one_ne_zero ) (quoted P ho m d v)).event
 filter_upwards [ ( heard P ho m 6 ).2,( heard P ho m d ).2,readyK P ho m h ht he ] with i hi hu hf
 change (Convention ( Row ( V i ) P.stock )).refund.charge ( Row ( V i ) P.stock d v )= _; unfold Convention; rw [hi,hu]; exact Warp.trading _ _ hf ((he i).trans_ne one_ne_zero) _
-- maybe variable cost peal.E.Frame. 
end positionR
end YM.FVAAlt2.Moving.Budget
