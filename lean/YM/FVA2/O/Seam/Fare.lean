import YM.FVA2.O.Seam.Coat
/-!
# Match at an intermediate large length

Its log-scale `amber`: a fixed fraction of the exterior log-scale θ i
(chosen based on required degree n). Then both early-time crossing bounds
(via the spare scale ratio between these two) and the upper-time estimates
from there can serve our `Need` (see `priceN`, `arriveN`, `Seam/Finish`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse
open scoped Topology ContDiff Interval
variable {G:Gauge} {I W : Type} {P:Geo I} {B: Deck G}{K: Booked B}{M: MS_Data G K} {u v:I→ ℝ}{n m d k:ℕ}
variable {F H:Glade G I} { Y X:T ( Glade G I )}
def eps (n:ℕ): ℝ:= eps_gain/(2*( (n:ℝ)+eps_gain ))
lemma eps_pos (n:ℕ): 0< eps n:= by unfold eps; exact div_pos p_gain (by have hs:= p_gain; positivity) -- ns ?
lemma eps_lt (n:ℕ): eps n<1:= by unfold eps; exact ( div_lt_one (by have hp:=p_gain; positivity) ).mpr (by have hp:=p_gain; linarith)
lemma eps_price (n:ℕ): (eps n)*((n:ℝ)+eps_gain)= eps_gain/2:= by unfold eps; field_simp
abbrev amber (P:Geo I)(n:ℕ)(i:I):= (1-eps n)*P.θ i
lemma amber_nn (i:I): 0 ≤ amber P n i:= mul_nonneg ( sub_nonneg.mpr (eps_lt n|>.le)) ( P.room i )
lemma amber_le (P:Geo I)(n:ℕ)(i:I): amber P n i≤ P.θ i:= (mul_le_mul_of_nonneg_right ( show 1 - eps n≤ 1 from sub_le_self _ (eps_pos n|>.le) ) ( P.room i )).trans ( one_mul _|>.le )
def later (P:Geo I)(n:ℕ):IntervalFamily I:={
    beg:= amber P n
    beg_nn := amber_nn
    window i:= Set.Ici ( amber P n i )
    ci _:= Subset.rfl
    used _:= Set.mem_Ici.mpr le_rfl
    ord _:= ordConnected_Ici
    logPart:= habitat P
    lg:=(Station P).lg }
local notation "A0" => later P n
lemma later_all (P:Geo I)(n:ℕ): Every (later P n):= fun _=>rfl
lemma later_live : liveP (face A0) P.η:= live_v ( show allowance _ _ from fun i=> (liveS (P:=P)).allow i )
abbrev Beg (P:Geo I)(n:ℕ) := initial (later P n)
def brow (P:Geo I)(n:ℕ)(i:I): ( Gulf P ).time := ⟨ i, ⟨ amber P n i,amber_nn i,amber_le P n i ⟩⟩
def montage (i:( Gulf P ).time): early P:= ⟨ i.1,i.2.val,i.2.property.2 ⟩
lemma Begin_w (P:Geo I)(n:ℕ): Way (Beg P n) (Mid P) (brow P n):= by
    refine ⟨fun _=>rfl,fun _=>rfl,fun i=>?_⟩; change habitat P i*(1+|amber P n i|)= habitat P i *(1+( amber P n i)); rw [abs_of_nonneg (amber_nn i)]
lemma mid_way : Way (Mid P) (deckB P) montage := ⟨fun _=>rfl,fun _=>rfl,fun _=>rfl⟩
lemma Way.comp { α β γ : Type } {S:Home α I}{T:Home β I}{U:Home γ I}{f:α→ β}{g:β→γ}(h:Way T U g)(hp:Way S T f) : Way S U (g∘ f):= ⟨ fun _=>( h.owner _ ).trans (hp.owner _),fun _=>( h.clock _ ).trans (hp.clock _),fun _=>(h.basic _).trans (hp.basic _) ⟩
abbrev wayUP (P:Geo I)(n:ℕ)(i:I): (Station P).Inst:= ( leveling ( P:=P ) ( brow P n i ))
lemma wayU (P:Geo I)(n:ℕ): Way (Beg P n) (face (Station P)) (wayUP P n):= Way.comp Mid.way ( Begin_w P n )
abbrev Need (P:Geo I)(n:ℕ)(i:I):ℝ:= exp (- ( ( n:ℝ ) + eps_gain/2 )* P.θ i)
lemma need_nn : nn ( Need P n ):= fun _=> (exp_pos _).le
local notation "S"=> Beg P n
lemma begin_live : liveP S P.η:= by
    intro i; exact ( norm_add_le .. ).trans (by change |P.η i|+|amber P n i|≤ _; rw [abs_of_nonneg (amber_nn i)]; change |P.η i| + amber P n i≤ (1+|P.η i|)*(1+( amber P n i )); nlinarith [abs_nonneg ( P.η i ), amber_nn (n:=n) (P:=P) i ])
lemma arriveN (h:Tiny (Mid P) P F): totalT S F (Need P n) false:= by
    obtain ⟨b,hb⟩:= exists_nat_gt (((n:ℝ)+eps_gain/2)/eps n); refine FormP.stays ( ( Begin_w P n ).tiny h b ) (fun i=>?_); apply exp_le_exp.mpr; obtain he:= (div_lt_iff₀ (eps_pos n)).mp hb; rw [Int.cast_natCast]; change _*( amber P n i - P.θ i)≤ _; unfold amber
    nlinarith [ mul_le_mul_of_nonneg_right he.le ( P.room i ) ]
lemma noonN (hc:paidC (Station P) F k): totalT (Beg P n) F (decay (Station P) k ∘ wayUP P n) false := ( wayU P n ).tax ( from_cost ( show Latch.Lease false false _ _ _ from hc ) ) rfl
local notation "L_"=> Beg P (m+k)
lemma tax_lo (P:Geo I)(m k:ℕ)(i:I): Cool.stamp ( Beg P (m+k) ).toScale (-(m:ℤ)) i * decay (Station P) k ( wayUP P (m+k) i ) = Need P (m+k) i:= by
    let n:= m+k; let t:= amber P n i; change (exp t ^ (-(m:ℤ)))*((exp t^(-(k:ℤ)))*exp (-eps_gain*t))= exp (- ((n:ℝ)+eps_gain/2)*P.θ i); simp_rw [ ← Real.rpow_intCast, ← Real.exp_mul,← Real.exp_add ]; congr 1; obtain hp:= eps_price n; have he:(n:ℝ)=(m:ℝ)+(k:ℝ):= Nat.cast_add m k; push_cast; unfold t amber; rw [he] at hp ⊢; -- he rew at self issue
    linear_combination ( P.θ i ) * hp
lemma priceN [LinearOrder W]{s: Finset W}{x:Position W I}{R: W→Label B}(hp:separable x)(hm:height R s=m)(ht:Colorable ( Station P ) X d k)(hv:n<d): totalT (Beg P (m+k)) ( rootT P M x R s X n ) (Need P (m+k)) false:= by
    subst m; refine FormP.stays ( bond_le ( k:=d ) ( fun m' h=> W_pay hp begin_live m' ) (fun i hi=> noonN ( ht i hi )) (fun _=>posS _|>.le ) (fun i=> decay_p ( wayUP P (height R s+k) i )) hv ) ( fun i=>?_ ); exact ( tax_lo P (height R s) k i ).le
end YM.FVA2.O.Seam
