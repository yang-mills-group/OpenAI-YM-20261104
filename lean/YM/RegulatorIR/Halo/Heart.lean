import YM.RegulatorIR.Halo.Wave

/-!
# Gauge consequences of repeat-read along rescaled orbit integration
Multiplicities not paid by hypothesized report growth. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset Sight
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {G:Gauge}{f c:Side}{s a b r p:ℕ}
section One
variable (x:ℝ→ Horizon G f)(h:ContDiffAt ℝ ∞ x 0) (H:Even f.val)(m:Side)
include h
lemma noted (k:ℕ): Full (W:=Side) (fun m=>vow (peel (Halo.signed m x))) k := by
 intro i hi; let σ (y: Book G f):= ‖coeff i (vow (peel x) y)‖ₑ
 refine ⟨Finset.univ.sup σ, ne_of_lt (Finset.sup_lt_iff (by simp)|>.mpr fun y _=> enorm_lt_top),?_⟩
 rintro m ⟨u,v⟩; let p:=castEdge m f u.val; let f'(t:ℝ):= x t (index p) v
 have hh : f'= fun t=> peel x t (index p,v):=rfl
 apply le_trans _ (Finset.le_sup (s:= Finset.univ) (f:=σ) (Finset.mem_univ (index p,v)))
 change ‖coeff i (tale (fun t=> fire (x t) p v))‖ₑ≤ ‖coeff i (tale f')‖ₑ
 unfold fire; split_ifs
 · exact le_rfl
 have ht: ContDiffAt ℝ ∞ f' 0:= RangeR.lifts (x:=x) h (index p,v)
 change ‖coeff i (tale (-f'))‖ₑ ≤ _; rw [show tale _= -tale f' from tale_neg ht, map_neg]; simp
variable {l P:ℝ} (he:l*f.val=P) {Q:Tariff (Foot G)} {T: Packet (Foot G) r}
local notation "A" => Carto G l P H he
local notation "C" => playS m (G:=G) H he
lemma multiplied (i:ℕ) {v:ℝ≥0∞}(hv:v≠⊤)(F: localQ Q T v)(hr:(A).Ready T) : rhyme (vow (peel (Halo.signed m x))) ((C).deckSum T) i = counts m * rhyme (vow (peel x)) ((A).deckSum T) i:=by
 cases Nat.eq_zero_or_pos r with
 | inl t=> subst r; simp [rhyme, Deck.deckSum]
 | inr t =>
    let q:= filament (render ((A).deckSum T)) (peel x); let u:= signed m x;let E:= (C).deckSum T;let g:=filament (render E) (peel u);let f:=fun _:ℝ=> counts m
    have heq: g=f*q:= funext fun j=> projected H he m _ hr ⟨0,t⟩ hv F (x j)
    let d:=churn (peel x) (render ((A).deckSum T)); let V:= churn (peel u) (render E)
    have hp : V=PowerSeries.C (counts m)*d:=by
       refine PowerSeries.ext ?_
       have hx := ink _ (RangeR.lifts h) (render ((A).deckSum T)); have hh:= ink _ (RangeR.lifts (wave m h)) (render ((C).deckSum T))
       change Script V g at hh; rw [heq] at hh
       intro i; exact congr_fun (Aspiration.unique hh (Script.mul (Script.oneC (counts m)) hx)) i
    rw [rhyme_f,rhyme_f]; change coeff i V=counts m*coeff i d;rw [hp,coeff_C_mul]
end One

section Hist
variable {W:Type}{M:W→ℕ}{n:Page M→Side}{q:ℕ}
variable {S:Heir n G}(H:Reel S)(T:S.Accounts)
variable {L:Meter W}

-- perVac consumer input

def haloT (i:Page M):Orders (Book G (n i)):=fun k l=> (S.maps i).deckSum (T.bulk i k l)
variable (w:W)(i:ℕ)(h:i<M w)
def ticketE (w:W)(i:ℕ)(h:i<M w):= (Flap.mk w i h).prev
variable {h'} (x : ℝ→ Horizon G (n (Page.mk w i h')))
local notation "v" => Page.mk w i h'
local notation "P" => tele H T w
local notation "Q" => eternal H w
variable (hx:ContDiffAt ℝ ∞ x 0)(hc: Common H)
include hx hc

-- product reexpression exact at fine event
variable (B: S.Supplies T L p q)
include B
lemma canonC (hH: Sym (S.maps v) (S.maps v) (H.stem v))(hS:Billed (H.stem v))(X:Side){j:ℕ}(hp:j ≤ p) :
 let g:= grove H w hc; let u:=Aug.sheet w i h' X; let y:= signed (Sight.slab X) x
 coeff j (money (g.stance u) (haloT P u) y)=counts (Sight.slab X) * coeff j (money (H.stance v) (haloT T v) x):=by
 intro g u y; let s:= Sight.slab X
 let f:= n v
 have hp' (u':Horizon G (n v)) : beneath (g.stance u) (stamped f s u')=counts s * beneath (H.stance v) u':=by
    let K:= fmat (Sight.radar H w u) (Sight.radar H w u) (H.stem v)
    have ht: Sym (S.maps v) (S.maps v) (H.stem v):=hH
    rw [H.realms] at ht
    unfold Reel.stance
    change beneath K _=_*beneath (fmat (S.maps v) (S.maps v) _) u'; rw [H.realms]; exact stiff s _ _ u' ht hS -- args check
 have hh (i):i=j → coeff i (tale (steam (g.stance u) ∘ y))=counts s * coeff i (tale (steam (H.stance v) ∘ x)):=by
    intro _; let f:=steam (H.stance v) ∘ x
    rw [show steam (g.stance u) ∘ y=(fun _=>counts s)*f from ?_,tale_mul (f:=fun _=>counts s) (g:=f) contDiffAt_const ((steam_smooth _).contDiffAt.comp _ hx), tale_const, PowerSeries.coeff_C_mul]
    ext t;change -beneath _ _=counts s*(-beneath _ _);rw [show beneath (g.stance u) (y t)= _ from hp' (x t)];ring
 unfold money;rw [map_add,map_add, mul_add, hh j rfl]; apply congr_arg; rw [rhyme_tube,rhyme_tube]
 unfold rhymeR;rw [Finset.mul_sum];apply sum_congr rfl;intro l hl;rw [Finset.mul_sum]; apply sum_congr rfl;intro d _
 have hi : l.1≤p:=by have he:=mem_antidiagonal.mp hl;omega
 obtain ⟨c,hc',hs⟩:= B.bulk_price l.1 hi d
 have he':=(B.bulk_deck v l.1 d hi);rw [H.realms] at he';change rhyme (vow _) (((Q).maps u).deckSum _) _=counts s*rhyme _ ((S.maps v).deckSum _) _; rw [H.realms]; exact multiplied x hx (H.even _) _ _ _ (hc'.cost v) (hs v) he'

-- original consumer
omit hx hc B
lemma canonical (y:ℝ→ Horizon G (n (ticketE w i h))) (hy:ContDiffAt ℝ ∞ y 0) (hc:Common H) (B:S.Supplies T L p q) (X:Side){j:ℕ}(hp:j ≤ p) :
 let g:= grove H w hc; let u:=Aug.sheet w i h.le X; let v':=ticketE w i h; let q:= signed (Sight.slab X) y
 coeff j (money (g.stance u) (haloT P u) q)=counts (Sight.slab X) * coeff j (money (H.stance v') (haloT T v') y):= canonC H T w i y hy hc B (H.moduli ⟨w,i,h⟩).sym.1 (H.moduli ⟨w,i,h⟩).rows.1 X hp
end Hist
end YM.RegulatorIR.Halo
