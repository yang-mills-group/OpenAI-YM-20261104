import YM.FormalBulk08.North.Feather

/-! Finite-order limiting families preserve normalization and symmetries. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.North
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster Dove Dove.Lab PowerSeries
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{E e r:ℕ}{W:Lab G K I}
-- hold truncated Rite up to E

def Charter {n:Side}(p:Pap (wire G n))(E:ℕ):Prop:= ∀ (s: Signed)(x: Site n)(I:Type)[Fintype I] (a b : Jets.Rays I → Jets.Rays (wire G n))(k: Jets.Rays I → Site n→G.El), a 0=0 → b 0=0 → ContDiffAt ℝ ω a 0 → ContDiffAt ℝ ω b 0 → Army k 0 → (∃ g:G.El,k 0=fun _=> g) → (∀ᶠ z in 𝓝 0,input G n (b z)=Lattice.gauge (k z) (pull s x (input G n (a z)))) → Through E (roam ℝ (motor a) p) (roam ℝ (motor b) p)
lemma robust_stamp (p:Side→Pap I)(t:Pap I)[Fintype I](N:ℕ→ℕ)(a b:I→Pap J) (he:∀ j≤ E,∀ n l,N j<l → marble l (coeff j (p n))=0)(h:∀ j≤E,∀ r,0<r →∀ v,Tendsto (fun n=>marble r (coeff j (p n)) v) atTop (𝓝 (marble r (coeff j t) v)))(hp:∀ n,Through E (roam ℝ a (p n)) (roam ℝ b (p n))): Through E (roam ℝ a t) (roam ℝ b t):= by
   intro m hm
   have hT j (hj:j≤E) l (hl:N j<l) : marble l (coeff j t)=0:=funext fun v=> tendsto_nhds_unique (h j hj l (by omega) v) (tendsto_const_nhds.congr' (.of_forall fun n=> (congr_fun (he _ hj _ _ hl) v).symm))
   apply sub_eq_zero.mp; rw [slime]; ext1 d; simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_zero]
   let f(j:ℕ):= insertAt ℝ a (coeff j t)-insertAt ℝ b (coeff j t);let g j n:= insertAt ℝ a (coeff j (p n))-insertAt ℝ b (coeff j (p n))
   have H (j) (hj:j∈Finset.range (m+1)): Tendsto (fun n=>MvPolynomial.coeff d (coeff m (g j n*X^j))) atTop (𝓝 (MvPolynomial.coeff d (coeff m (f j*X^j)))):= by
       have hM: j≤E:=by rw [Finset.mem_range] at hj;omega
       simpa only [one_mul,g,f] using Shore.lab m j a b d p t (fun _=>1) (N j) (.of_forall (he j hM)) (hT j hM) (fun r hr v=>by simpa using h j hM r hr v)
   exact tendsto_nhds_unique (tendsto_finsetSum _ H) (tendsto_const_nhds.congr' (.of_forall fun n=> by dsimp only;rw [←MvPolynomial.coeff_sum]; unfold g; rw [←slime,hp n m hm,sub_self,MvPolynomial.coeff_zero]))

variable (a:hue G)(hp:Use W ρ E)(h:LocalRatio ρ)(hs:G.Simple)(x:Leaf W.scrolls)(n:Side)
omit n in
lemma highlim : Tendsto (fun n:Side=>n.val) atTop atTop := tendsto_atTop.mpr fun k=> (eventually_ge_atTop (⟨k+1,by omega⟩:Side)).mono fun n hn=>Nat.le_trans (Nat.le_succ _) hn
include hp h hs
lemma clamps : Charter (stone (heir a ρ W x.a x.b) n) E := by
    let T i:=saga ρ a W x.a (i+x.b) x.b; let V:=heir a ρ W x.a x.b; let S(i: Side):= stone (T i.val) n
    have ht(k:ℕ): FrameV (T k) _:=genu (W.V x.a) (W.wood x.a) (W.toEmpire.bill x.a) ρ a h hs (N:=k+x.b) (i:=x.b) (by omega)
    have hv:=born a x hp h hs
    have hu j (he:j≤ E) r (z:Fin r):
        marble r (coeff j (stone V n)) = cum z n (V j r):= by
       rw [←stopper_presents he]; change rancho _ _ _ =_; rw [hv.flower _ _ z n];exact congr_arg (fun p=> cum z n (p r)) (show stopper V E j=V j from if_pos he)
    intro s y I inst b c k hb hc hB hC hk hz hx; refine robust_stamp S _ (fun j=>j+2) (motor b) (motor c) ?_ ?_ (fun n i _=> by rw [show roam _ _ _ = _ from (ht _).civic _ s y I _ _ _ hb hc hB hC hk hz hx]) -- hp implicit eq
    · intro j he q l hl;rw [show marble l _= _ from (ht q.val).flower _ l (⟨0,by omega⟩ : Fin l) n]
      have hh: T q.val j l=0:=by by_contra hh;exact (not_le.mpr hl) ((ht _).valence _ _ hh).2.1
      rw [hh,cum_zero]
    intro j he r hr v; let z:Fin r:=⟨0,hr⟩;rw [show marble r _=_ from hu j he r z]; simp_rw [show ∀ a:Side, marble r (coeff j (S a)) = cum z n (T a.val j r) from fun a=> (ht _).flower j r z n];
    apply Tendsto.comp (g:=fun k:ℕ=> cum z n (T k j r) v) _ highlim
    obtain hv':= totem_hold (r:=r) a hp h hs x he; let δ:=fun i=> fare_n x (i+x.b); obtain ⟨B,b,hb'⟩:= hv'.left; obtain ⟨D,d,hd⟩:=hv'.right; obtain ⟨A,u,u',hA⟩:=hv'.nebula; have he1: Up (V j r):= by
        rw [show V j=_ from (show stopper V E j=V j from if_pos he).symm];exact hv.civil _ _
    have hz:Faint staticT δ (fun i=>cum z n (T i j r) v-cum z n (V j r) v):= by
        have ha:0≤ W.windowD x:=(hp.zero x).le; refine ⟨_,u,u',fun i=>?_⟩
        have hx: cum z n (T i j r)-cum z n (V j r)=cum z n (T i j r-V j r):= by funext; exact ((funds_vat z n ha (hb' i) _).tsum_sub (funds_vat z n ha (hd i) _)).symm
        exact le_trans (le_of_eq (congr_arg abs (congr_fun hx v))) ((cum_charge z n (Aster.up_sub ((ht i).civil j r) he1) ha (hA i)).value ha v z)
    convert (quietude (δ:=δ) ((tendsto_add_atTop_iff_nat x.b).2 (fare_fin x)) (fun i=>(ratioR_pos ..).le) hz).add_const (cum z n (V j r) v) using 1; · ext i; simp
    rw [zero_add]

lemma vacancy (he:e≤ E) (b c:Axis)(i j: hue G){f:Cover→ℝ}(hV:Pad f):
    Ends (fun m=> Cork.net (saga ρ a W x.a m x.b e 2) b c i j f) (Cork.net (heir a ρ W x.a x.b e 2) b c i j f):= by
    apply (tendsto_add_atTop_iff_nat x.b).mp; obtain ⟨⟨B,W',Y⟩,⟨D,d,Q⟩,C,hc,c',H⟩:= totem_hold (r:=2) a hp h hs x he; let δ:=fun i=> fare_n x (i+x.b); let y l:= saga ρ a W x.a (l+x.b) x.b e 2; let F:=heir a ρ W x.a x.b e 2
    have hz: Faint staticT δ (fun k=> Cork.net (y k) b c i j f-Cork.net F b c i j f):= by
       obtain ⟨n,R,P⟩:=hV;have ht:=hp.zero x; obtain ⟨A,p,L⟩:= net_funding (G:=G) n ht; refine ⟨_,hc.times (soft_coin _ (R*A)),fun i=>mul_nonneg (c' i) (mul_nonneg P.1 p.le),fun k=>?_⟩
       dsimp only;rw [mul_right_comm,← Cork.net_sub (T:=y k) (S:=F) ⟨_,_,ht,Y k⟩ ⟨_,_,ht,Q 0⟩ _ _ _ _ ⟨_,_,P⟩]; exact L _ _ P _ _ (H k) b c i j
    convert (quietude ((tendsto_add_atTop_iff_nat x.b).mpr (fare_fin x)) (fun i=>(ratioR_pos ..).le) hz).add_const (Cork.net F b c i j f) using 1
    · ext k; rw [sub_add_cancel]
    rw [zero_add]
lemma limited_seal (he:e≤ E)(hz:0<e) : Cork.Null (heir a ρ W x.a x.b e 2):= by
    have hy:∀ᶠ m:ℕ in atTop,Cork.Null (saga ρ a W x.a m x.b e 2):=(eventually_ge_atTop x.b).mono fun m hm=> (genu (W.V x.a) (W.wood x.a) (W.toEmpire.bill x.a) ρ a h hs hm).seals _ hz
    exact ⟨fun i j u v=>tendsto_nhds_unique (vacancy a hp h hs x he i j u v (flat_pad 1)) (tendsto_const_nhds.congr' (hy.mono fun _ ht=> (ht.bottom ..).symm)),fun i j u v k=> tendsto_nhds_unique (vacancy a hp h hs x he i j u v (Pad.ch k)) (tendsto_const_nhds.congr' (hy.mono fun _ ht=> (ht.air ..).symm)),fun i j u v k l=> tendsto_nhds_unique (vacancy a hp h hs x he i j u v ((Pad.ch k).mul (Pad.ch l))) (tendsto_const_nhds.congr' (hy.mono fun _ ht=>(ht.water ..).symm))⟩
lemma capital (u:hue G) : value u (heir a ρ W x.a x.b 0 2)=1:= by
    apply tendsto_nhds_unique (vacancy a hp h hs x (Nat.zero_le _) 1 1 u u ((Pad.ch 0).mul (Pad.ch 0))); refine tendsto_const_nhds.congr' ?_; filter_upwards [eventually_ge_atTop x.b] with m hm
    change 1=value u (model (W.V x.a) _ _ _ _ _ _ _ _); rw [(genu (W.V x.a) (W.wood x.a) (W.toEmpire.bill x.a) ρ a h hs hm).ink,pink_weigh K.penalty K.penalty_pos ((W.V x.a).clock.adm _)]
end YM.FormalBulk08.North
