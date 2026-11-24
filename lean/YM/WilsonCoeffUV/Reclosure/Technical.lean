import YM.WilsonCoeffUV.Reclosure.Assemble
import YM.WilsonCoeffUV.Vacuum.UV.Budget
/-!
# Render consumer. fixed demand tail ages; can pay post length fees
for all these assemblies by a parallel price. This never estimates actual
Rep.eval stability under representation change.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Near PowerSeries Supply Ticket Realm
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}{s S a b u v:ℝ}{W X F:Canvas G}{n:ℕ}{T:Credit}

lemma Desc.join (h:Desc F e s a)(p:Desc W e s a)(hv:∀ r,Amber terrain s b (F e r-W e r))(hs:0<s): Desc (F-W) e s b:=by
   refine ⟨h.toPointV.sub p.toPointV,hv,?_, fun i=>clothAware (h.beats 2) (p.beats 2) hs (h.aft i) (p.aft i)⟩
   intro r b x; simp only [Pi.sub_apply]; rw [h.sign,p.sign]; ring
lemma these {A:Levels G}{Ñ:ChartRatio G}(h:G.Simple)(g:LocalRatio Ñ)(p:m≤ n)(w:∀ r,Amber terrain s a (actionW A Ñ n m i r)): Desc (actionW A Ñ n m) i s a:=by
   have hp:= catchment A Ñ h g p
   refine ⟨⟨fun x b=>hp.separate x b i,hp.pureU _,hp.center _,mural_finite h g p i,?_⟩,w,spin_has hp.signs,fun i=>hp.affine _ i.ne'⟩
   intro j hj; rcases hj with hj|hj
   · interval_cases j; · exact congr_fun (congr_fun hp.empty.symm i) 0
     exact hp.vanishes _
   exact hp.rank _ _ (by omega)
lemma across (R:Realm G e T)(h:R.anchor≤m)(p: i≤ e)(w:∀ r, Amber terrain s a (timeless R.draws R.paid m i r)) : Desc (timeless R.draws R.paid m) i s a:= by
    have H:= modern R h
    refine ⟨⟨H.lamp i p,H.purePoints _ p,H.tor _ p,fun r=>H.lit _ r p,?_⟩,w,H.s i p 2,H.aware _ p⟩
    intro j hj; rcases hj with hj|hj
    · interval_cases j; · exact H.barren _ p
      exact H.zero_color _ p
    exact H.holds _ p _ hj

def retWidth (G:Gauge)(e :ℕ)(s:ℝ)(h:0<s):= (authored G e s h).choose
def postask (G:Gauge)(e:ℕ)(s:ℝ)(h:0<s):= (authored G e s h).choose_spec.choose
lemma ret_pos (G:Gauge)(e:ℕ)(s:ℝ)(h:0<s): 0< retWidth G e s h:= (authored G e s h).choose_spec.choose_spec.1
lemma post_nn (G:Gauge)(e:ℕ)(s:ℝ)(h:0<s): 0≤ postask G e s h:= (authored G e s h).choose_spec.choose_spec.2.2.1
lemma attain (he:0<s)(h:0≤a)(p:∀ i< e,Desc F i s a) : ∃ W:SeriesA G, fromBefore W e ∧ sews W F e ∧ W.length=meterPre e ∧ desk W=stiles e ∧ seals W ∧ Draw W (retWidth G e s he) (a*postask G e s he):= (authored G e s he).choose_spec.choose_spec.2.2.2 _ _ h p

structure Inkplate {G:Gauge}{U:Credit}(e:ℕ)(R:Realm G e U)(T:Credit):Prop where
    costs m (h:R.anchor≤m)(i:ℕ): i≤ e+1→ postask G i (R.mint m h).σ (R.mint m h).width≤ R.cash T m
    reserves m (h:R.anchor≤ m)(i:ℕ): i≤ e+1 → (retWidth G i (R.mint m h).σ (R.mint m h).width)⁻¹ ≤ R.cash T m

-- add as many fixed curvature demands. pure after L.
variable {Ñ:ChartRatio G}{U:Credit}
def aftB (A:Levels G)(m e:ℕ)(Ñ:ChartRatio G)(c:ℝ)(h: 5≤ A.clock.J (m+1))(p:craftQuest A m e h):= let T:=quest A m Ñ h p
   ∀ i:ℕ,i≤e+1→ postask G i T.σ T.width≤c ∧ (retWidth G i T.σ T.width)⁻¹ ≤ c
lemma strawShelf (K:KernelChoices)(e r:ℕ)(Ñ:ChartRatio G): ∀ᶠ c:ℝ in atTop, ∀ (A:Levels G)(m:ℕ), A.clock.kernel=K→ A.clock.J (m+1)=r→ ∀ (h:5≤A.clock.J (m+1))(p:craftQuest A m e h), aftB A m e Ñ c h p:=by
   have HZ j:∀ᶠ c:ℝ in atTop, ∀ (A:Levels G)(m:ℕ), A.clock.kernel=K→ A.clock.J (m+1)=r→ A.clock.J m=j → ∀(h:5 ≤ A.clock.J (m+1))(p:craftQuest A m e h), aftB A m e Ñ c h p:=by
     by_cases z: 5 ≤ r∧4≤ j
     · let w:= cue G K j r z.2 z.1
       have hh i:∀ᶠ c:ℝ in atTop, postask G i w.outlet w.o_pos ≤ c ∧ (retWidth G i w.outlet w.o_pos)⁻¹ ≤ c:= (eventually_ge_atTop _).and (eventually_ge_atTop _)
       filter_upwards [(eventually_all_finset (Finset.range (e+2))).mpr (fun i _=>hh i)] with c hv; intro A m a b v u p y g; subst K r j; exact hv _ (Finset.mem_range.mpr (Nat.lt_succ_of_le g))
     refine Eventually.of_forall (fun c A m e p h t z'=>?_); subst K r j; exact False.elim (z ⟨t,A.clock.adm _⟩)
   filter_upwards [(eventually_all_finset (Finset.range (r+1))).mpr (fun i _=> HZ i)] with c hc; intro A m a b v p; subst K r
   exact hc _ (show A.clock.J m∈ _ from Finset.mem_range.mpr (Nat.lt_succ_of_le (A.fits.mono m.le_succ))) A m rfl rfl rfl v p

-- whichever Inkplate bill / anchor; reads within canonical width. these kernels include ALL completion vertices needed up to e (no hidden valence), differences allowed correlated glyphed DON't require uniqueness on nulls/path lifts.
structure DisplayA (G:Gauge)(R:SeriesA G)(σ A:ℝ)(e:ℕ)(F:Canvas G) :Prop where
    sewn : sews R F (e+1)
    placed : fromBefore R (e+1)
    charge : Draw R σ A
    length : R.length= meterPre (e+1)
    census : desk R=stiles (e+1)
    reads : seals R
variable {C:Credit}

def peak (R:Realm G e T)(m:ℕ)(h:R.anchor≤ m) :=retWidth G (e+1) (R.mint m h).σ (R.mint m h).width

theorem covenants (G:Gauge)(e:ℕ)(T U:Credit): ∃ V:Credit,∀ R:Realm G e T,Inkplate e R U→∀ m (h:R.anchor≤m), ∃ Y:SeriesA G,DisplayA G Y (peak R m h) (R.cash V m) e (timeless R.draws R.paid m) ∧ ∀ N ≥ m, ∃ Z:SeriesA G, DisplayA G Z (peak R m h) (R.cash V m * R.tempC m N) e (actionW R.draws R.paid N m-timeless R.draws R.paid m) ∧ sews (Y++Z) (actionW R.draws R.paid N m) (e+1) :=by
    obtain ⟨V,hV⟩:= full_vacuum G e T
    refine ⟨V.prodC U,fun R P m h=>?_⟩
    have he:= R.depth m h; have hv:0≤ V.buy (R.y m):= zero_le_one.trans (Credit.purchase _ he)
    let A:=V.buy (R.y m); let I:= R.mint m h
    let Z:= timeless R.draws R.paid m
    have hb N (p:m ≤ N) i (hg:i<e+1) r: PairA I.σ A (R.tempC m N) (actionW R.draws R.paid N m i r) (Z i r):= inherited (hV i (by omega) r) R h p le_rfl
    have hx i (p:i<e+1) : Desc Z i I.σ A:= across R h (by omega) fun r=>(hb m le_rfl i p r).vale
    obtain ⟨Y,y,w,c,g,G',b⟩:=attain I.width hv hx
    have hh:=P.costs _ h (e+1) le_rfl
    have hy : A*postask G (e+1) I.σ I.width ≤ R.cash (V.prodC U) m:=by unfold Realm.cash; rw [Credit.products]; exact mul_le_mul_of_nonneg_left hh hv
    refine ⟨Y,⟨w,y,b.light le_rfl hy,c,g,G'⟩,?_⟩; intro N hn
    have hl :0≤ R.tempC m N:= (PathCost.trail_pos ..).le
    let F:= actionW R.draws R.paid N m
    have H i (p:i<e+1): Desc (F-Z) i I.σ (A*R.tempC m N):= (these R.hG R.green hn fun r=> (hb N hn i p r).pose).join (hx i p) (fun r=> (hb N hn i p r).visit) I.width
    obtain ⟨W,o,d,x,X,x',z⟩:= attain I.width (mul_nonneg hv hl) H
    refine ⟨W,⟨d,o,z.light le_rfl ?_,x,X,x'⟩,fun j hj=>?_⟩
    · rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right hy hl
    rw [murals_append, Pi.add_apply, w j hj,d j hj]; change Z j+(F j-Z j)=F j; abel
end YM.WilsonCoeffUV.Bank.Mosaic
