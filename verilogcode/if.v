module top(
    input wire a,    // 输入信号
    input wire b,    // 输入信号
    output reg out   // 输出信号
);

always @ (a or b) begin
    if (a == 1'b1) begin
        out = b;   // 如果 a 为 1，则赋值 out 为 b
    end else begin
        out = 1'b0; // 如果 a 为 0，则赋值 out 为 0
    end
end

endmodule