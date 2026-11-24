import YM.LocalTaylorR2.Grafting.Upsize
/-! adapt LocalTaylorR2/Orbit/Banker: late gate + spare doubling in all captains & uniform over same threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (X:Coat T F) (H:Cash W s μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G} (χ:Chi) (p:H.ThinP)
local notation "Θ"=>p.val
local notation "Ω"=> (M.signs S)
open Gas Ursell Trees Tail Port Charge Marker
variable {j l k n:ℕ} {θ β v y d :ℝ}
open Reserves Tender
open CalendarStep
def rise (Q:YM.ConnectedActivityE6.Target G P)(Γ:Target.Expense Q)(L:Side)(W μ x:ℝ)(o:Target.Order G W)(j m l:ℕ)(χ:Chi)(ε:ℝ):Prop:=
    ∃ A₀ a' C d v t r B D x' b y K θ ρ w l' n, CartAge Q L W μ x ε (Γ.one/2) w D x' r K θ ρ (b+b) j n m l ∧ b+b ≤ Q.goal L x ∧
      ∀ (c f:Side) (S:StepData c f) (T:Tube G S), Stamp T → ∀ R C' (H:Cash W x μ L Q o C' T R),
      ∃ N:Captain H j C d v t A₀ a' r B y (n+j) χ, LocalBookingsR2 (l+1:ℝ) b N.conduit ∧ StoresR2 H j v d A₀ D l' x' n χ ∧ Marker.Tinted G x K d o.a L χ j

lemma rising (P:Teller G)(Q:YM.ConnectedActivityE6.Target G P)(Γ:Target.Expense Q):∃ n:ℕ,∀ L:Side,n≤ L.val→ ∀ W μ o j h l χ ε, (0:ℝ)< ε →0<W→ 0<μ →(∃ D:Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j)→ ∀ᶠ x in atTop, rise Q Γ L W μ x o j h l χ ε:=by
   obtain ⟨k,H⟩:= Marker.scripts P Q
   refine ⟨k,fun L hx W μ o j h l χ ε he hw hμ hoff=> ?_⟩
   obtain ⟨D,hd,hL,hX⟩:=hoff; obtain ⟨θ,hθ,hΘ⟩:= Series.allowance l j
   obtain ⟨e,hp,hh,hl⟩:= Tail.plan l ε he
   obtain ⟨s,hs,hE⟩:= exists_between (show -(1/2:ℝ)< min Q.rate (-e) from lt_min Q.start (by linarith)); obtain ⟨hS,hE⟩:= lt_min_iff.mp hE
   obtain ⟨a,a',C,d,v,w,r,B,k,D',x',b,K,l',n,hB,hr,hb,hD,hA,hK,hM⟩:= H L hx s (l+1) hs hS (by positivity) D hd j χ W hw μ hμ o
   let t:=max (e+s) Q.rate; obtain ⟨u,ht,h'⟩:= exists_between (show t<0 from max_lt (by linarith) Q.stop)
   let Y:= fun x=> betaF G x L; let ρ x:=Y x^e; let q x:=Y x^u; let δ:=Γ.one/2
   let Bk x:= b x+b x; have hP:=hb.add hb
   obtain ⟨hm,hx⟩:= cargo (θ:=θ) D' Bk x' r K ρ l n j Rate.power hP hD hA hr hK hμ (le_max_left ..) (le_max_right ..)
   have hy(i:ℕ)(hp:i ≤l+1):= Tail.height (L:=L) G i j h 1 e δ u (requested i ε) (by have h:= hl i hp; unfold requested at *; linarith)
   have hy':= eventually_all.mpr (fun i:Fin (l+2)=> hy i (Nat.le_of_lt_succ i.isLt))
   filter_upwards [(Work.E09.betaF_growth G L).eventually_ge_atTop 1,(Tail.meters _ hm Q.δ).below (show t<0 from ht.trans h') (1/2) (by norm_num), (Tail.meters (G:=G) q (show Rate G L u q from Rate.power) δ).below h' (1/2) (by norm_num), ((Rate.power (a:=e)).mul hP).below (by linarith) 1 zero_lt_one,
     Tail.marked (L:=L) Q hμ (l+1:ℝ), hx u ht,hy',(Blush.efferv (G:=G) (L:=L) hμ (-(l:ℝ)-2)) (-((l:ℝ)+1)) (by linarith),hM,hP Q.rate hS] with x hh0 h1 h2 h3 h4 h5 hx h6 h7 h8
   have hρ : 1≤ ρ x:= Real.one_le_rpow hh0 hp.le
   have hg : ρ x ^ (l+1) ≤ betaF G x L^(l+1:ℝ):= by
     rw [show ρ x ^(l+1)=_ from (Real.rpow_mul_natCast (zero_le_one.trans hh0) e (l+1)).symm]; apply Real.rpow_le_rpow_of_exponent_le hh0; push_cast; nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) l,hp] -- use mul
   refine ⟨a,a',C,d x,v x,w x,r x,B x,D' x,x' x,b x,k x,K x,θ,ρ x,q x,l',n,⟨hh0,hθ,hρ,Real.rpow_pos_of_pos (zero_lt_one.trans_le hh0) _,hΘ,(le_abs_self _).trans h3,hg,h4,(le_abs_self _).trans h1,(le_abs_self _).trans h5,(le_abs_self _).trans h2,fun i h => (le_abs_self _).trans (hx (⟨i,Nat.lt_succ_of_le h⟩: Fin _)),(le_abs_self _).trans h6⟩,(le_abs_self _).trans h8, fun c f S T ht R C' H=>?_⟩ -- script tuple order
   obtain ⟨V,hp,hD,hh⟩:= h7 c f S T ((H.laws.data.funds).patch hL hX) ht R C' H; exact ⟨V,hp,hD,hh.2⟩
end YM.LocalTaylorR2.Orbit
