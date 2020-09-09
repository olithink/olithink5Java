import java.awt.Color;
import javax.swing.JPanel;

/**
 * @author Oliver Brausch 25.11.2009
 */
public class Square extends JPanel {
	private static final long serialVersionUID = 1L;
					
	public Square(int col, int row) {
		super.setBounds(col*70, (7-row)*70, 70, 70);
		super.setBackground((col + row) % 2 == 1 ? new Color(216, 216, 216) : new Color(64, 64, 64));
	}	
}
