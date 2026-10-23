import ManuscriptTerminal

open MeasureTheory Set Filter Asakura.Chapter4
open scoped Topology
namespace BarrierManuscript

noncomputable def call (k x w : ℝ) : ℝ := put (-k) (-x) w
noncomputable def truncatedCall (b k x w : ℝ) : ℝ :=
  (x-k)*(normalCDF ((b-x)/w)-normalCDF ((k-x)/w))-
    w*(phi ((b-x)/w)-phi ((k-x)/w))

theorem call_formula (k x w : ℝ) :
    call k x w=(x-k)*normalCDF ((x-k)/w)+w*phi ((x-k)/w) := by
  unfold call put
  congr 1 <;> congr 1 <;> ring

theorem call_put_parity (k x w : ℝ) : call k x w-put k x w=x-k := by
  rw [call_formula]
  unfold put
  rw [show (x-k)/w=-((k-x)/w) by ring,normalCDF_neg,phi_even]
  ring

/-- The UOC reflection formula, including the digital term at the absorbing
boundary. This is an identity of the displayed pricing functions. -/
theorem truncated_call_reflection (b k x w : ℝ) :
    truncatedCall b k x w-truncatedCall b k (2*b-x) w =
      call k x w-call k (2*b-x) w+k-x+2*(b-k)*normalCDF ((b-x)/w) := by
  have h1 := call_put_parity k x w
  have h2 := call_put_parity k (2*b-x) w
  unfold truncatedCall
  rw [show (b-(2*b-x))/w=-((b-x)/w) by ring,normalCDF_neg,phi_even]
  unfold put at h1 h2
  linarith only [h1,h2]

/-- The equivalent UOP/survival decomposition in Bachelier. -/
theorem uoc_put_survival_decomposition (b k x w : ℝ) :
    truncatedCall b k x w-truncatedCall b k (2*b-x) w =
      killedPut b k x w+x-b+(b-k)*(2*normalCDF ((b-x)/w)-1) := by
  rw [truncated_call_reflection]
  have h1 := call_put_parity k x w
  have h2 := call_put_parity k (2*b-x) w
  unfold killedPut
  linarith only [h1,h2]

/-- Reflection of the stock transforms the DOC formula into the UOP formula. -/
theorem doc_uop_reflection (b k x w : ℝ) :
    call k x w-call k (2*b-x) w = killedPut (-b) (-k) (-x) w := by
  unfold call killedPut
  congr 1
  congr 1
  ring

theorem knock_in_out_payoff (hit : Prop) [Decidable hit] (payoff : ℝ) :
    (if hit then payoff else 0)=payoff-(if hit then 0 else payoff) := by
  split_ifs <;> ring

theorem uip_reflection (b k x w : ℝ) :
    put k x w-killedPut b k x w=put k (2*b-x) w := by
  unfold killedPut
  ring

end BarrierManuscript
#print axioms BarrierManuscript.call_formula
#print axioms BarrierManuscript.call_put_parity
#print axioms BarrierManuscript.truncated_call_reflection
#print axioms BarrierManuscript.uoc_put_survival_decomposition
#print axioms BarrierManuscript.doc_uop_reflection
#print axioms BarrierManuscript.knock_in_out_payoff
#print axioms BarrierManuscript.uip_reflection
