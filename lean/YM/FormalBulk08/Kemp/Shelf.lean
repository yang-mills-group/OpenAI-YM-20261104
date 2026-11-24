import YM.FormalBulk08.Kemp.Ornate

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J: Type*} {η θ A B : ℝ} {l i u j t r : ℕ}

lemma cut_charge {V X:Type*}{W: Reach V}{U : Reach X}{f:X→V}(h:Injective f)(hu:∀ i j,U.d i j = W.d (f i) (f j)) {K:Tile V r} (x:X)(he:Knoxville W η (f x) K B): Knoxville U η x (jetty f K) B:= by
    refine ⟨he.1,le_trans ?_ ((ENNReal.tsum_comp_le_tsum_of_injective (f:=fun v:chain X r=>f ∘ v) (fun p q hv=>funext fun i=>h (congr_fun hv i)) (penon W (f x) η K)).trans he.2)⟩
    apply le_of_eq; apply tsum_congr; intro v;unfold penon herb; rw [←Fin.comp_cons];simp_rw [wide, Function.comp_apply, hu];rfl
lemma kalm_cut {T:Tile (Biglot (I⊕J)) r}{P:(n:Side)→Tile (Tor n (I⊕J)) r}{x:Biglot J}(h:Kalm η (coastRight _ _ _ x) T P) : Kalm η x (jetty (coastRight _ _ _) T) (fun n=> jetty (coastRight _ _ _) (P n)):= by
    obtain ⟨h,C,H⟩:=h; exact ⟨fun v=> h (coastRight _ _ _ ∘ v),C,H.mono fun n hn=> cut_charge (W:=lake n (I⊕J)) (U:=lake n J) (f:=coastRight (Site n) I J) (fun i j hv=>Prod.ext (show (coastRight _ I _ i).1=(coastRight _ I _ j).1 from congr_arg Prod.fst hv) (Sum.inr_injective (show (coastRight _ I _ i).2=(coastRight _ I _ j).2 from congr_arg Prod.snd hv))) (fun _ _=>rfl) (Lotus.drip n x) hn⟩
lemma kalm_group [Fintype I]{p:Waves (Biglot I)}{A:(n:Side)→Waves (Tor n I)}{T:OrbitV (Biglot I)}{V : (n:Side)→OrbitV (Tor n I)}{B:ℝ}{o}
   (i e R r:ℕ)(q)(M)(hp:∀ n r j, n ≤ i → r≤R → 0<j → Kith η (p n r j) (fun s=> A s n r j))(h:∀ n j,n≤R→ Kalm η o (T n j) (fun s=> V s n j))
   (he:e≤ R)(hs:Wind q M)(hθ:0<η)(hw:∀ᶠ n in atTop, Grate (lake n _) η (M n) B)(ho:∀ n i j,M n i j=M n j i):
     Kalm η o (dipper q p T i e r) (fun n=>dipper (M n) (A n) (V n) i e r):= by
    induction i using Nat.strong_induction_on generalizing e r with
    | _ i ih=> cases i with
               | zero=> simp_rw [dipper_first];exact h e r he
               | succ i=>
                 simp_rw [dipper_succ]
                 have hz (d:ℕ)(hd:d ≤ i) (e r) (hr:e≤R): Kalm η o (dipper q p T d e r) (fun n=>dipper (M n) (A n) (V n) d e r):= ih d (by omega) e r (fun n b k hv=> hp n b k (by omega)) hr
                 refine ((kalm_stare (hz i le_rfl _ _ he) hs _ hθ hw).add ((?_ : Kalm η o _ _).smul _)).smul _
                 unfold brawl Lava.reach; apply kalm_many _; intro a ha; apply kalm_many _; intro b hb; apply kalm_many _; intro w hw'
                 rw [Finset.mem_antidiagonal] at ha hb; simp_rw [visor_eq]; exact ((kalm_bond (hp b.1 a.1 _ (by omega) (by omega) (by omega)) (hz b.2 (by omega) _ _ (by omega)) hs _ hθ hw ho).polish).larger _

variable (K : KernelChoices)(P:Flight j t)(V:Lodge P.patch)(Z:Pot G)
-- mark is at fine origin given Z (already shifted input)

def sailors {K : KernelChoices} (h:P.patch.Branches K G) (Z:Pot G)(l : ℕ)(n: Side):= joust (saddleP G (primary P.patch K n) V) (lever (ferry P h V n) (Reef.seat (Reef.floor K P V n) (banner l Z _)))
def coves : OrbitV (Biglot (BoardL G P.patch V)) := fun e r=> Glide.urn P V G K (Z e r)
lemma rename_income [Fintype I][Fintype J](M:I→J→ℝ)(F: Pap I)(e r):rancho (PowerSeries.map (mixRows M).toRingHom F) e r=pearl M (rancho F e r):= by rw [rancho,coeff_map]; exact Lava.target ..
lemma tor_yolk {n f : Side} (S:StepData n f)(K:Lodge S.patch)(F:Pap (wire G f))(e r): rancho (joust (saddleP G S K) (Reef.seat K.forest F)) e r=pearl ((pane G S.patch K).acts n) (pearl ((winging (Rim G S.patch) (Loc G 1)).acts n) (jetty (splitCo S.ratio (Loc G 1)).symm (rancho F e r))):= by
    unfold Reef.seat; rw [becoming S K, Bank.yarn, show rancho (PowerSeries.map (mixRows ((pane G S.patch K).acts n)).toRingHom _) e r= _ from rename_income _ _ _ _, show rancho (PowerSeries.map (mixRows ((winging (Rim G S.patch) (Loc G 1)).acts n)).toRingHom _) e r= _ from rename_income _ _ _ _, joust_level]; rfl
lemma fees_tor {K:KernelChoices}(h:P.patch.Branches K G)(hv:Young Z l)(hA:∀ e r,Agate (Z e r))(hf:l≤u)(n:Side)(e r:ℕ)(hs:0 < η)(hp:0≤A)(hk:(Flight.duo K.penalty P).A0.strip η A) :
    rancho (sailors P V h Z u n) e r= pearl ((zealand K P V G).acts n) (pearl ((pane G P.patch V).acts n) (pearl ((winging (Rim G P.patch) (Loc G 1)).acts n) (sieve n (altitude P.patch Z e r)))) := by
    let S:=primary P.patch K n;let F:=banner u Z (n*P.L)
    rw [sailors,shifted P V h n _ η A hs hp hk]
    have hv' : jetty (splitCo S.ratio (Loc G 1)).symm (rancho F e r)=sieve n (altitude P.patch Z e r):= by
       rw [show rancho F e r=_ from badge Z hv hA hf _ e r]; exact (rinse _ (Z e r) S.ratio).symm
    let T:= joust (saddleP G S V) (Reef.seat (V.forest (S:=S)) F);let A': Matrix (Tor n (BoardL G P.patch V)) (Tor n (BoardL G P.patch V)) ℝ:= (zealand K P V G).acts n
    have he : rancho (joust (saddleP G S V) (Reef.seat (V.forest (S:=S)) F)) e r=_ := (tor_yolk S V F e r).trans (congr_arg (fun v=>pearl ((pane G S.patch V).acts n) (pearl ((winging (Bank.Rim G S.patch) (Loc G 1)).acts n) v)) hv') -- Δ
    exact (rename_income A' T e r).trans (congr_arg (pearl A') he)
end YM.FormalBulk08.Kemp
