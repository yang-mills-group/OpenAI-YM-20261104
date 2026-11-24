import YM.WilsonCoeffUV.Vacuum.Step.Tokenizer
/-! Commit to instantiated recurrence without constraining steps *after*
prescribed packing (fit widths/costs on stamps BEFORE L).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M m k r b j:ℕ}

lemma Ballast.partial {α β: Type*} {U V: ropes Cover α β}{s A θ κ:ℝ}(h:Ballast s A θ U V)(he:θ≤κ): Ballast s A κ U V:= ⟨h.oneP,h.otherP,h.between.le (mul_le_mul_of_nonneg_left he h.nn)⟩
-- word of rates matrix norm charges known.
variable {I:Gear G} {A: Levels G}{Ñ: ChartRatio G}
lemma ordered_spurs (g:LocalRatio Ñ) (h:m<N)(k:ℕ)(hs:G.Simple): spurs (loose A m) A.clock.kernel Ñ (shuttleM (conditional A N m)) (shuttleM (feedA A N m)) (actionW A Ñ N (m+1)) k 0=0:= by
   have he:= resin A N m h
   have hb:= (A.blocks m 0).branches
   let H:= old A Ñ hs g N (m+1) h
   have hv t:= spurs_enter (loose A m) A.clock.kernel Ñ _ _ _ hb g H.patch he k 0 t
   ext1 r; apply (hv r).unique
   apply Yields.zero.congr; apply Eventually.of_forall; intro n
   have hh : (xray (mStep A n m) (xree (loose A m) A.clock.kernel n) (freeForms A N (m+1)) (roam A N m n) Ñ ((story A Ñ N (m+1)).1 (n*(loose A m).L)) k 0)=0 := bare_abr _ (pack_zero _ g) k
   rw [hh]; rfl

-- `Frame`: schedule costs for both gear length choices.
structure Usage (A:Levels G)(Ñ:ChartRatio G)(m:ℕ) where
   past: ℝ
   s:ℝ
   σ:ℝ
   preB:ℝ
   sig:ℝ
   D:ℝ
   width:0<σ
   win : σ<s
   depth:0<past
   credit : 1≤D
   due :0≤ preB
   sumS:0≤ sig
   lift : s/(loose A m).L.val ≤past
   cardG : Glint A m s preB sig D

namespace Usage
variable (U: Usage A Ñ m)
def gear : Gear G:= ⟨loose A m,A.clock.kernel,Ñ,U.past,U.s,U.σ,U.width,U.win,U.depth,U.lift,U.preB,U.sig,U.D,U.due,U.sumS,U.credit⟩

def postStand (p:m<N)(g:G.Simple)(h:LocalRatio Ñ) : Stand U.gear := by
   let Z:= freshet A Ñ N m
   have he:= catchment A Ñ g h (show m+1≤N from p)
   have hv:= perch A Ñ g h p
   refine {
     page := actionW A Ñ N (m+1)
     M:= shuttleM (groove A N m)
     Q:= shuttleM (feedA A N m)
     T:= shuttleM (wagon A N m)
     Z:=plain G (freeForms A N m)
     R:=shuttleM (conditional A N m)
     crank:= U.cardG.main _ p
     rule:= pass_width A N m p
     topQ:= U.cardG.single N p.le
     rolls:= U.cardG.θ N p
     sym:=he.pureU
     move:=he.center
     even_page:=he.separate
     bit:= fun i hi=>he.affine i hi.ne'
     negative:= fun k=>ordered_spurs h p k g
     mint:= crown_read g A ..
     lead:= hv.lead
     ez:= fun i=> (hv.growth i 2).cover }
lemma postStake (p:m<N)(g:G.Simple)(h:LocalRatio Ñ) : (U.postStand p g h).stake=actionW A Ñ N m:= (conduct A Ñ p).symm

def runs (k r:ℕ)(d x:ℝ)(N M:ℕ): Prop:= ∀ i j, lowerGrade i j k r → PairA U.past x d (actionW A Ñ N (m+1) i j) (actionW A Ñ M (m+1) i j)

def readPast (g:G.Simple)(h: LocalRatio Ñ)(x θ:ℝ)(ht:1≤x)(he:m+1≤b)(p:b≤N)(q:b≤M)(h₀ : rag A m b≤θ)(h₁: rag A (m+1) b≤θ)(hw:U.runs k r θ x N M): Rally k r U.gear :=
  { P:= U.postStand (he.trans p) g h
    Q:= U.postStand (he.trans q) g h
    x:=x
    σ:=θ
    θ := le_trans (Real.sqrt_nonneg _) h₀
    rich:=ht
    paid:=hw
    Υ:= (U.cardG.shift _ _ _ he p q).1.partial h₁
    Χ:= (U.cardG.shift _ _ _ he p q).2.partial h₁
    Ω:= (U.cardG.kite b N M (by omega) p q).partial h₀ }
-- main estimates after digest win.
end Usage

def carryD (G:Gauge)(k r:ℕ):= (purse G k r).choose
def carryF (G:Gauge)(k r:ℕ)(I:Gear G):= ((purse G k r).choose_spec I).choose
lemma carryF_nn (k r:ℕ)(I:Gear G): 0≤ carryF G k r I:= ((purse G k r).choose_spec I).choose_spec.1
lemma gate (I:Gear G)(R:Rally (k+1) (r+2) I)(h:I.towing r)(e v:ℝ): Amber terrain I.past e (R.P.page (k+1) (r+2))→Amber terrain I.past e (R.Q.page (k+1) (r+2))→Amber terrain I.past v (R.P.page (k+1) (r+2)- R.Q.page (k+1) (r+2))→Kept R (carryD G k r) (carryF G k r I) e v:= ((purse G k r).choose_spec I).choose_spec.2 R h e v

-- ready recurrence: fixed domains; absolute without stride carrying posts.
lemma toll_energy (U:Usage A Ñ m)(g:G.Simple)(h: LocalRatio Ñ)(p:m<N)(ht: U.gear.towing r)(B x:ℝ)(hp:1≤x)(hk:∀ i j,lowerGrade i j (k+1) (r+2)→ Amber terrain U.past x (actionW A Ñ N (m+1) i j))(he:Amber terrain U.past B (actionW A Ñ N (m+1) (k+1) (r+2))) :
    Amber terrain U.σ (U.gear.gain r*B/(loose A m).L.val+carryF G k r U.gear*x^carryD G k r) (actionW A Ñ N m (k+1) (r+2)):=by
    let θ:= max (rag A m N) (rag A (m+1) N); have hy:0≤θ:= le_max_of_le_left (Real.sqrt_nonneg _)
    let R:= U.readPast g h x θ hp (show m+1≤N from p) (le_refl N) (le_refl N) (le_max_left ..) (le_max_right ..) (show U.runs (k+1) (r+2) θ x N N from fun i j b=> PairA.echo (hk i j b) hy)
    rw [← U.postStake p g h]; exact (gate U.gear R ht B 0 he he (by change Amber terrain U.past 0 (_- _); exact (show Amber terrain U.past 0 (actionW A Ñ N (m+1) (k+1) (r+2)-actionW A Ñ N (m+1) (k+1) (r+2)) from by rw [sub_self]; exact Amber.zero))).front
lemma toll_range (U:Usage A Ñ m)(g:G.Simple)(h:LocalRatio Ñ)(Q x V θ:ℝ)(ht:1≤x)(hp:m+1≤b)(p:b≤N)(q:b≤M)(h₀ : rag A m b≤θ)(h₁: rag A (m+1) b≤θ)(hi:U.gear.towing r)(hw:U.runs (k+1) (r+2) θ x N M) (hx:Amber terrain U.past Q (actionW A Ñ N (m+1) (k+1) (r+2)))(hf:Amber terrain U.past Q (actionW A Ñ M (m+1) (k+1) (r+2)))(hl:Amber terrain U.past V (actionW A Ñ N (m+1) (k+1) (r+2)-actionW A Ñ M (m+1) (k+1) (r+2))):
     Amber terrain U.σ (U.gear.gain r*V/(loose A m).L.val+carryF G k r U.gear*x^carryD G k r*(1+Q)*θ) (actionW A Ñ N m (k+1) (r+2)-actionW A Ñ M m (k+1) (r+2)):=by
   rw [← U.postStake (show m<N from hp.trans p) g h,← U.postStake (show m<M from hp.trans q) g h]; exact (gate U.gear (U.readPast g h x θ ht hp p q h₀ h₁ hw) hi Q V hx hf hl).gap
end YM.WilsonCoeffUV.Bank
