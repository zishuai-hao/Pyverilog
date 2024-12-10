module top(CLK, RST);
  input CLK, RST;
  reg [3:0] cnt;
  always @(posedge CLK) begin
      case(cnt)
        'h0, 'h1: begin
          cnt <= cnt + 1;
        end
        'h2: begin
          cnt <= cnt + 2;
        end
        'hf: begin
          cnt <= 0;
        end
        default: begin
          cnt <= cnt + 1;
        end
      endcase
    end
endmodule
